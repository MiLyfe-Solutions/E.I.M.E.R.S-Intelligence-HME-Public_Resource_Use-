import V185TrunkScan23Chunk0884

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5238009 : List Nat := [1, 2, 1, 3, 1, 1, 4, 4, 1, 1, 4]
def baseStart_5238009 : Nat := 118140960795 + 5238009 * 2 ^ 59
def prefixEnd_5238009 : Nat := 4983230072969 + 3 ^ 40 * 5238009 * 2
def baseEnd_5238009 : Nat := 2689616289576501999398341

theorem tailTrace_5238009 : CollatzResearch.WordTrace tailWord_5238009 prefixEnd_5238009 2689616289576501999398341 := by
  unfold tailWord_5238009
  simp only [CollatzResearch.WordTrace]
  refine ⟨191045883280595448561101081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127363922187063632374067387 191045883280595448561101081)
  ·
    refine ⟨143284412460446586420825811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191045883280595448561101081 143284412460446586420825811)
    ·
      refine ⟨214926618690669879631238717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143284412460446586420825811 214926618690669879631238717)
      ·
        refine ⟨80597482009001204861714519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214926618690669879631238717 80597482009001204861714519)
        ·
          refine ⟨120896223013501807292571779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80597482009001204861714519 120896223013501807292571779)
          ·
            refine ⟨181344334520252710938857669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120896223013501807292571779 181344334520252710938857669)
            ·
              refine ⟨34002062722547383301035813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181344334520252710938857669 34002062722547383301035813)
              ·
                refine ⟨6375386760477634368944215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34002062722547383301035813 6375386760477634368944215)
                ·
                  refine ⟨9563080140716451553416323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6375386760477634368944215 9563080140716451553416323)
                  ·
                    refine ⟨14344620211074677330124485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9563080140716451553416323 14344620211074677330124485)
                    ·
                      refine ⟨2689616289576501999398341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14344620211074677330124485 2689616289576501999398341)
                      ·
                        rfl

theorem cell23_5238009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_5238009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238009 prefixEnd_5238009 := by exact prefixLift 5238009
  have htrace : WordTrace (prefixWord ++ tailWord_5238009) baseStart_5238009 baseEnd_5238009 := by
    simpa [prefixWord, tailWord_5238009, baseEnd_5238009] using wordTrace_append hprefix tailTrace_5238009
  have hstable : (prefixWord ++ tailWord_5238009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238009).length < 2 ^ (prefixWord ++ tailWord_5238009).sum := by decide
  have hdescent : baseEnd_5238009 < baseStart_5238009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238020 : List Nat := [2, 3, 2, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_5238020 : Nat := 118140960795 + 5238020 * 2 ^ 59
def prefixEnd_5238020 : Nat := 4983230072969 + 3 ^ 40 * 5238020 * 2
def baseEnd_5238020 : Nat := 2689621937863701456360791

theorem tailTrace_5238020 : CollatzResearch.WordTrace tailWord_5238020 prefixEnd_5238020 2689621937863701456360791 := by
  unfold tailWord_5238020
  simp only [CollatzResearch.WordTrace]
  refine ⟨95523142241777798719875757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127364189655703731626501009 95523142241777798719875757)
  ·
    refine ⟨35821178340666674519953409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95523142241777798719875757 35821178340666674519953409)
    ·
      refine ⟨26865883755500005889965057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35821178340666674519953409 26865883755500005889965057)
      ·
        refine ⟨20149412816625004417473793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26865883755500005889965057 20149412816625004417473793)
        ·
          refine ⟨15112059612468753313105345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20149412816625004417473793 15112059612468753313105345)
          ·
            refine ⟨11334044709351564984829009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15112059612468753313105345 11334044709351564984829009)
            ·
              refine ⟨8500533532013673738621757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11334044709351564984829009 8500533532013673738621757)
              ·
                refine ⟨3187700074505127651983159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8500533532013673738621757 3187700074505127651983159)
                ·
                  refine ⟨4781550111757691477974739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3187700074505127651983159 4781550111757691477974739)
                  ·
                    refine ⟨7172325167636537216962109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4781550111757691477974739 7172325167636537216962109)
                    ·
                      refine ⟨2689621937863701456360791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7172325167636537216962109 2689621937863701456360791)
                      ·
                        rfl

theorem cell23_5238020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_5238020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238020 prefixEnd_5238020 := by exact prefixLift 5238020
  have htrace : WordTrace (prefixWord ++ tailWord_5238020) baseStart_5238020 baseEnd_5238020 := by
    simpa [prefixWord, tailWord_5238020, baseEnd_5238020] using wordTrace_append hprefix tailTrace_5238020
  have hstable : (prefixWord ++ tailWord_5238020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238020).length < 2 ^ (prefixWord ++ tailWord_5238020).sum := by decide
  have hdescent : baseEnd_5238020 < baseStart_5238020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238026 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2]
def baseStart_5238026 : Nat := 118140960795 + 5238026 * 2 ^ 59
def prefixEnd_5238026 : Nat := 4983230072969 + 3 ^ 40 * 5238026 * 2
def baseEnd_5238026 : Nat := 2689625018747628432885763

theorem tailTrace_5238026 : CollatzResearch.WordTrace tailWord_5238026 prefixEnd_5238026 2689625018747628432885763 := by
  unfold tailWord_5238026
  simp only [CollatzResearch.WordTrace]
  refine ⟨47761625830383465116117483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127364335547689240309646621 47761625830383465116117483)
  ·
    refine ⟨71642438745575197674176225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47761625830383465116117483 71642438745575197674176225)
    ·
      refine ⟨53731829059181398255632169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71642438745575197674176225 53731829059181398255632169)
      ·
        refine ⟨40298871794386048691724127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53731829059181398255632169 40298871794386048691724127)
        ·
          refine ⟨60448307691579073037586191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40298871794386048691724127 60448307691579073037586191)
          ·
            refine ⟨90672461537368609556379287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60448307691579073037586191 90672461537368609556379287)
            ·
              refine ⟨136008692306052914334568931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90672461537368609556379287 136008692306052914334568931)
              ·
                refine ⟨204013038459079371501853397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136008692306052914334568931 204013038459079371501853397)
                ·
                  refine ⟨4781555588884672769574689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 204013038459079371501853397 4781555588884672769574689)
                  ·
                    refine ⟨3586166691663504577181017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4781555588884672769574689 3586166691663504577181017)
                    ·
                      refine ⟨2689625018747628432885763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586166691663504577181017 2689625018747628432885763)
                      ·
                        rfl

theorem cell23_5238026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_5238026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238026 prefixEnd_5238026 := by exact prefixLift 5238026
  have htrace : WordTrace (prefixWord ++ tailWord_5238026) baseStart_5238026 baseEnd_5238026 := by
    simpa [prefixWord, tailWord_5238026, baseEnd_5238026] using wordTrace_append hprefix tailTrace_5238026
  have hstable : (prefixWord ++ tailWord_5238026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238026).length < 2 ^ (prefixWord ++ tailWord_5238026).sum := by decide
  have hdescent : baseEnd_5238026 < baseStart_5238026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238053 : List Nat := [1, 3, 1, 2, 4, 2, 3, 1, 2, 4]
def baseStart_5238053 : Nat := 118140960795 + 5238053 * 2 ^ 59
def prefixEnd_5238053 : Nat := 4983230072969 + 3 ^ 40 * 5238053 * 2
def baseEnd_5238053 : Nat := 896546294241766609082713

theorem tailTrace_5238053 : CollatzResearch.WordTrace tailWord_5238053 prefixEnd_5238053 896546294241766609082713 := by
  unfold tailWord_5238053
  simp only [CollatzResearch.WordTrace]
  refine ⟨191047488092436044075702813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127364992061624029383801875 191047488092436044075702813)
  ·
    refine ⟨71642808034663516528388555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191047488092436044075702813 71642808034663516528388555)
    ·
      refine ⟨107464212051995274792582833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71642808034663516528388555 107464212051995274792582833)
      ·
        refine ⟨80598159038996456094437125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107464212051995274792582833 80598159038996456094437125)
        ·
          refine ⟨15112154819811835517706961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80598159038996456094437125 15112154819811835517706961)
          ·
            refine ⟨11334116114858876638280221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15112154819811835517706961 11334116114858876638280221)
            ·
              refine ⟨4250293543072078739355083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11334116114858876638280221 4250293543072078739355083)
              ·
                refine ⟨6375440314608118109032625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4250293543072078739355083 6375440314608118109032625)
                ·
                  refine ⟨4781580235956088581774469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6375440314608118109032625 4781580235956088581774469)
                  ·
                    refine ⟨896546294241766609082713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4781580235956088581774469 896546294241766609082713)
                    ·
                      rfl

theorem cell23_5238053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_5238053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238053 prefixEnd_5238053 := by exact prefixLift 5238053
  have htrace : WordTrace (prefixWord ++ tailWord_5238053) baseStart_5238053 baseEnd_5238053 := by
    simpa [prefixWord, tailWord_5238053, baseEnd_5238053] using wordTrace_append hprefix tailTrace_5238053
  have hstable : (prefixWord ++ tailWord_5238053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238053).length < 2 ^ (prefixWord ++ tailWord_5238053).sum := by decide
  have hdescent : baseEnd_5238053 < baseStart_5238053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238056 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_5238056 : Nat := 118140960795 + 5238056 * 2 ^ 59
def prefixEnd_5238056 : Nat := 4983230072969 + 3 ^ 40 * 5238056 * 2
def baseEnd_5238056 : Nat := 2689640423167263315510625

theorem tailTrace_5238056 : CollatzResearch.WordTrace tailWord_5238056 prefixEnd_5238056 2689640423167263315510625 := by
  unfold tailWord_5238056
  simp only [CollatzResearch.WordTrace]
  refine ⟨95523798755712587794031011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127365065007616783725374681 95523798755712587794031011)
  ·
    refine ⟨143285698133568881691046517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95523798755712587794031011 143285698133568881691046517)
    ·
      refine ⟨13433034200022082658535611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143285698133568881691046517 13433034200022082658535611)
      ·
        refine ⟨20149551300033123987803417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13433034200022082658535611 20149551300033123987803417)
        ·
          refine ⟨15112163475024842990852563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20149551300033123987803417 15112163475024842990852563)
          ·
            refine ⟨22668245212537264486278845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15112163475024842990852563 22668245212537264486278845)
            ·
              refine ⟨8500591954701474182354567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22668245212537264486278845 8500591954701474182354567)
              ·
                refine ⟨12750887932052211273531851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8500591954701474182354567 12750887932052211273531851)
                ·
                  refine ⟨19126331898078316910297777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12750887932052211273531851 19126331898078316910297777)
                  ·
                    refine ⟨14344748923558737682723333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19126331898078316910297777 14344748923558737682723333)
                    ·
                      refine ⟨2689640423167263315510625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14344748923558737682723333 2689640423167263315510625)
                      ·
                        rfl

theorem cell23_5238056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_5238056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238056 prefixEnd_5238056 := by exact prefixLift 5238056
  have htrace : WordTrace (prefixWord ++ tailWord_5238056) baseStart_5238056 baseEnd_5238056 := by
    simpa [prefixWord, tailWord_5238056, baseEnd_5238056] using wordTrace_append hprefix tailTrace_5238056
  have hstable : (prefixWord ++ tailWord_5238056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238056).length < 2 ^ (prefixWord ++ tailWord_5238056).sum := by decide
  have hdescent : baseEnd_5238056 < baseStart_5238056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238066 : List Nat := [3, 2, 1, 1, 4, 3, 2, 7]
def baseStart_5238066 : Nat := 118140960795 + 5238066 * 2 ^ 59
def prefixEnd_5238066 : Nat := 4983230072969 + 3 ^ 40 * 5238066 * 2
def baseEnd_5238066 : Nat := 99616502147178084310577

theorem tailTrace_5238066 : CollatzResearch.WordTrace tailWord_5238066 prefixEnd_5238066 99616502147178084310577 := by
  unfold tailWord_5238066
  simp only [CollatzResearch.WordTrace]
  refine ⟨47761990560347236823981513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127365308160925964863950701 47761990560347236823981513)
  ·
    refine ⟨35821492920260427617986135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47761990560347236823981513 35821492920260427617986135)
    ·
      refine ⟨53732239380390641426979203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35821492920260427617986135 53732239380390641426979203)
      ·
        refine ⟨80598359070585962140468805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53732239380390641426979203 80598359070585962140468805)
        ·
          refine ⟨15112192325734867901337901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80598359070585962140468805 15112192325734867901337901)
          ·
            refine ⟨5667072122150575463001713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15112192325734867901337901 5667072122150575463001713)
            ·
              refine ⟨4250304091612931597251285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5667072122150575463001713 4250304091612931597251285)
              ·
                refine ⟨99616502147178084310577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4250304091612931597251285 99616502147178084310577)
                ·
                  rfl

theorem cell23_5238066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 7].length) (baseStart_5238066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238066 prefixEnd_5238066 := by exact prefixLift 5238066
  have htrace : WordTrace (prefixWord ++ tailWord_5238066) baseStart_5238066 baseEnd_5238066 := by
    simpa [prefixWord, tailWord_5238066, baseEnd_5238066] using wordTrace_append hprefix tailTrace_5238066
  have hstable : (prefixWord ++ tailWord_5238066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238066).length < 2 ^ (prefixWord ++ tailWord_5238066).sum := by decide
  have hdescent : baseEnd_5238066 < baseStart_5238066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238076 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_5238076 : Nat := 118140960795 + 5238076 * 2 ^ 59
def prefixEnd_5238076 : Nat := 4983230072969 + 3 ^ 40 * 5238076 * 2
def baseEnd_5238076 : Nat := 2689650692780353237260533

theorem tailTrace_5238076 : CollatzResearch.WordTrace tailWord_5238076 prefixEnd_5238076 2689650692780353237260533 := by
  unfold tailWord_5238076
  simp only [CollatzResearch.WordTrace]
  refine ⟨95524163485676359501895041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127365551314235146002526721 95524163485676359501895041)
  ·
    refine ⟨71643122614257269626421281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95524163485676359501895041 71643122614257269626421281)
    ·
      refine ⟨53732341960692952219815961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71643122614257269626421281 53732341960692952219815961)
      ·
        refine ⟨40299256470519714164861971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53732341960692952219815961 40299256470519714164861971)
        ·
          refine ⟨60448884705779571247292957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40299256470519714164861971 60448884705779571247292957)
          ·
            refine ⟨22668331764667339217734859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60448884705779571247292957 22668331764667339217734859)
            ·
              refine ⟨34002497647001008826602289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22668331764667339217734859 34002497647001008826602289)
              ·
                refine ⟨25501873235250756619951717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34002497647001008826602289 25501873235250756619951717)
                ·
                  refine ⟨4781601231609516866240947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25501873235250756619951717 4781601231609516866240947)
                  ·
                    refine ⟨7172401847414275299361421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4781601231609516866240947 7172401847414275299361421)
                    ·
                      refine ⟨2689650692780353237260533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7172401847414275299361421 2689650692780353237260533)
                      ·
                        rfl

theorem cell23_5238076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_5238076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238076 prefixEnd_5238076 := by exact prefixLift 5238076
  have htrace : WordTrace (prefixWord ++ tailWord_5238076) baseStart_5238076 baseEnd_5238076 := by
    simpa [prefixWord, tailWord_5238076, baseEnd_5238076] using wordTrace_append hprefix tailTrace_5238076
  have hstable : (prefixWord ++ tailWord_5238076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238076).length < 2 ^ (prefixWord ++ tailWord_5238076).sum := by decide
  have hdescent : baseEnd_5238076 < baseStart_5238076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238156 : List Nat := [2, 2, 1, 2, 1, 3, 3, 4, 5]
def baseStart_5238156 : Nat := 118140960795 + 5238156 * 2 ^ 59
def prefixEnd_5238156 : Nat := 4983230072969 + 3 ^ 40 * 5238156 * 2
def baseEnd_5238156 : Nat := 298854641248079213806685

theorem tailTrace_5238156 : CollatzResearch.WordTrace tailWord_5238156 prefixEnd_5238156 298854641248079213806685 := by
  unfold tailWord_5238156
  simp only [CollatzResearch.WordTrace]
  refine ⟨95525622405531446333351161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127367496540708595111134881 95525622405531446333351161)
  ·
    refine ⟨71644216804148584750013371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95525622405531446333351161 71644216804148584750013371)
    ·
      refine ⟨107466325206222877125020057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71644216804148584750013371 107466325206222877125020057)
      ·
        refine ⟨80599743904667157843765043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107466325206222877125020057 80599743904667157843765043)
        ·
          refine ⟨120899615857000736765647565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80599743904667157843765043 120899615857000736765647565)
          ·
            refine ⟨45337355946375276287117837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120899615857000736765647565 45337355946375276287117837)
            ·
              refine ⟨17001508479890728607669189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45337355946375276287117837 17001508479890728607669189)
              ·
                refine ⟨3187782839979511613937973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17001508479890728607669189 3187782839979511613937973)
                ·
                  refine ⟨298854641248079213806685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3187782839979511613937973 298854641248079213806685)
                  ·
                    rfl

theorem cell23_5238156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 5].length) (baseStart_5238156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238156 prefixEnd_5238156 := by exact prefixLift 5238156
  have htrace : WordTrace (prefixWord ++ tailWord_5238156) baseStart_5238156 baseEnd_5238156 := by
    simpa [prefixWord, tailWord_5238156, baseEnd_5238156] using wordTrace_append hprefix tailTrace_5238156
  have hstable : (prefixWord ++ tailWord_5238156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238156).length < 2 ^ (prefixWord ++ tailWord_5238156).sum := by decide
  have hdescent : baseEnd_5238156 < baseStart_5238156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238176 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 2, 5, 2]
def baseStart_5238176 : Nat := 118140960795 + 5238176 * 2 ^ 59
def prefixEnd_5238176 : Nat := 4983230072969 + 3 ^ 40 * 5238176 * 2
def baseEnd_5238176 : Nat := 2689702040845802846010073

theorem tailTrace_5238176 : CollatzResearch.WordTrace tailWord_5238176 prefixEnd_5238176 2689702040845802846010073 := by
  unfold tailWord_5238176
  simp only [CollatzResearch.WordTrace]
  refine ⟨95525987135495218041215191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127367982847326957388286921 95525987135495218041215191)
  ·
    refine ⟨143288980703242827061822787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95525987135495218041215191 143288980703242827061822787)
    ·
      refine ⟨214933471054864240592734181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143288980703242827061822787 214933471054864240592734181)
      ·
        refine ⟨40300025822787045111137659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214933471054864240592734181 40300025822787045111137659)
        ·
          refine ⟨60450038734180567666706489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40300025822787045111137659 60450038734180567666706489)
          ·
            refine ⟨45337529050635425750029867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60450038734180567666706489 45337529050635425750029867)
            ·
              refine ⟨68006293575953138625044801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45337529050635425750029867 68006293575953138625044801)
              ·
                refine ⟨51004720181964853968783601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68006293575953138625044801 51004720181964853968783601)
                ·
                  refine ⟨38253540136473640476587701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51004720181964853968783601 38253540136473640476587701)
                  ·
                    refine ⟨3586269387794403794680097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38253540136473640476587701 3586269387794403794680097)
                    ·
                      refine ⟨2689702040845802846010073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586269387794403794680097 2689702040845802846010073)
                      ·
                        rfl

theorem cell23_5238176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_5238176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238176 prefixEnd_5238176 := by exact prefixLift 5238176
  have htrace : WordTrace (prefixWord ++ tailWord_5238176) baseStart_5238176 baseEnd_5238176 := by
    simpa [prefixWord, tailWord_5238176, baseEnd_5238176] using wordTrace_append hprefix tailTrace_5238176
  have hstable : (prefixWord ++ tailWord_5238176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238176).length < 2 ^ (prefixWord ++ tailWord_5238176).sum := by decide
  have hdescent : baseEnd_5238176 < baseStart_5238176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238206 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_5238206 : Nat := 118140960795 + 5238206 * 2 ^ 59
def prefixEnd_5238206 : Nat := 4983230072969 + 3 ^ 40 * 5238206 * 2
def baseEnd_5238206 : Nat := 2689717445265437728634935

theorem tailTrace_5238206 : CollatzResearch.WordTrace tailWord_5238206 prefixEnd_5238206 2689717445265437728634935 := by
  unfold tailWord_5238206
  simp only [CollatzResearch.WordTrace]
  refine ⟨23881633557610218900752809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127368712307254500804014981 23881633557610218900752809)
  ·
    refine ⟨17911225168207664175564607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23881633557610218900752809 17911225168207664175564607)
    ·
      refine ⟨26866837752311496263346911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17911225168207664175564607 26866837752311496263346911)
      ·
        refine ⟨40300256628467244395020367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26866837752311496263346911 40300256628467244395020367)
        ·
          refine ⟨60450384942700866592530551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40300256628467244395020367 60450384942700866592530551)
          ·
            refine ⟨90675577414051299888795827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60450384942700866592530551 90675577414051299888795827)
            ·
              refine ⟨136013366121076949833193741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90675577414051299888795827 136013366121076949833193741)
              ·
                refine ⟨51005012295403856187447653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136013366121076949833193741 51005012295403856187447653)
                ·
                  refine ⟨9563439805388223035146435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51005012295403856187447653 9563439805388223035146435)
                  ·
                    refine ⟨14345159708082334552719653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9563439805388223035146435 14345159708082334552719653)
                    ·
                      refine ⟨2689717445265437728634935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14345159708082334552719653 2689717445265437728634935)
                      ·
                        rfl

theorem cell23_5238206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_5238206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238206 prefixEnd_5238206 := by exact prefixLift 5238206
  have htrace : WordTrace (prefixWord ++ tailWord_5238206) baseStart_5238206 baseEnd_5238206 := by
    simpa [prefixWord, tailWord_5238206, baseEnd_5238206] using wordTrace_append hprefix tailTrace_5238206
  have hstable : (prefixWord ++ tailWord_5238206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238206).length < 2 ^ (prefixWord ++ tailWord_5238206).sum := by decide
  have hdescent : baseEnd_5238206 < baseStart_5238206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238293 : List Nat := [1, 3, 2, 1, 3, 2, 3, 2, 1, 5]
def baseStart_5238293 : Nat := 118140960795 + 5238293 * 2 ^ 59
def prefixEnd_5238293 : Nat := 4983230072969 + 3 ^ 40 * 5238293 * 2
def baseEnd_5238293 : Nat := 896587372694126296082345

theorem tailTrace_5238293 : CollatzResearch.WordTrace tailWord_5238293 prefixEnd_5238293 896587372694126296082345 := by
  unfold tailWord_5238293
  simp only [CollatzResearch.WordTrace]
  refine ⟨191056241611566565064439533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127370827741044376709626355 191056241611566565064439533)
  ·
    refine ⟨71646090604337461899164825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191056241611566565064439533 71646090604337461899164825)
    ·
      refine ⟨53734567953253096424373619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71646090604337461899164825 53734567953253096424373619)
      ·
        refine ⟨80601851929879644636560429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53734567953253096424373619 80601851929879644636560429)
        ·
          refine ⟨30225694473704866738710161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80601851929879644636560429 30225694473704866738710161)
          ·
            refine ⟨22669270855278650054032621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30225694473704866738710161 22669270855278650054032621)
            ·
              refine ⟨8500976570729493770262233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22669270855278650054032621 8500976570729493770262233)
              ·
                refine ⟨6375732428047120327696675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8500976570729493770262233 6375732428047120327696675)
                ·
                  refine ⟨9563598642070680491545013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6375732428047120327696675 9563598642070680491545013)
                  ·
                    refine ⟨896587372694126296082345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9563598642070680491545013 896587372694126296082345)
                    ·
                      rfl

theorem cell23_5238293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_5238293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238293 prefixEnd_5238293 := by exact prefixLift 5238293
  have htrace : WordTrace (prefixWord ++ tailWord_5238293) baseStart_5238293 baseEnd_5238293 := by
    simpa [prefixWord, tailWord_5238293, baseEnd_5238293] using wordTrace_append hprefix tailTrace_5238293
  have hstable : (prefixWord ++ tailWord_5238293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238293).length < 2 ^ (prefixWord ++ tailWord_5238293).sum := by decide
  have hdescent : baseEnd_5238293 < baseStart_5238293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238299 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 5]
def baseStart_5238299 : Nat := 118140960795 + 5238299 * 2 ^ 59
def prefixEnd_5238299 : Nat := 4983230072969 + 3 ^ 40 * 5238299 * 2
def baseEnd_5238299 : Nat := 2689765198966305864772007

theorem tailTrace_5238299 : CollatzResearch.WordTrace tailWord_5238299 prefixEnd_5238299 2689765198966305864772007 := by
  unfold tailWord_5238299
  simp only [CollatzResearch.WordTrace]
  refine ⟨191056460449544828089157951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127370973633029885392771967 191056460449544828089157951)
  ·
    refine ⟨286584690674317242133736927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191056460449544828089157951 286584690674317242133736927)
    ·
      refine ⟨429877036011475863200605391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286584690674317242133736927 429877036011475863200605391)
      ·
        refine ⟨644815554017213794800908087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429877036011475863200605391 644815554017213794800908087)
        ·
          refine ⟨967223331025820692201362131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644815554017213794800908087 967223331025820692201362131)
          ·
            refine ⟨1450834996538731038302043197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967223331025820692201362131 1450834996538731038302043197)
            ·
              refine ⟨544063123702024139363266199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1450834996538731038302043197 544063123702024139363266199)
              ·
                refine ⟨816094685553036209044899299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544063123702024139363266199 816094685553036209044899299)
                ·
                  refine ⟨1224142028329554313567348949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 816094685553036209044899299 1224142028329554313567348949)
                  ·
                    refine ⟨28690828788973929224234741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1224142028329554313567348949 28690828788973929224234741)
                    ·
                      refine ⟨2689765198966305864772007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28690828788973929224234741 2689765198966305864772007)
                      ·
                        rfl

theorem cell23_5238299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 5].length) (baseStart_5238299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238299 prefixEnd_5238299 := by exact prefixLift 5238299
  have htrace : WordTrace (prefixWord ++ tailWord_5238299) baseStart_5238299 baseEnd_5238299 := by
    simpa [prefixWord, tailWord_5238299, baseEnd_5238299] using wordTrace_append hprefix tailTrace_5238299
  have hstable : (prefixWord ++ tailWord_5238299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238299).length < 2 ^ (prefixWord ++ tailWord_5238299).sum := by decide
  have hdescent : baseEnd_5238299 < baseStart_5238299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238300 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_5238300 : Nat := 118140960795 + 5238300 * 2 ^ 59
def prefixEnd_5238300 : Nat := 4983230072969 + 3 ^ 40 * 5238300 * 2
def baseEnd_5238300 : Nat := 2689765712446960360859503

theorem tailTrace_5238300 : CollatzResearch.WordTrace tailWord_5238300 prefixEnd_5238300 2689765712446960360859503 := by
  unfold tailWord_5238300
  simp only [CollatzResearch.WordTrace]
  refine ⟨95528248461270602629972177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127370997948360803506629569 95528248461270602629972177)
  ·
    refine ⟨71646186345952951972479133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95528248461270602629972177 71646186345952951972479133)
    ·
      refine ⟨26867319879732356989679675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71646186345952951972479133 26867319879732356989679675)
      ·
        refine ⟨40300979819598535484519513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26867319879732356989679675 40300979819598535484519513)
        ·
          refine ⟨30225734864698901613389635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40300979819598535484519513 30225734864698901613389635)
          ·
            refine ⟨45338602297048352420084453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30225734864698901613389635 45338602297048352420084453)
            ·
              refine ⟨8500987930696566078765835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45338602297048352420084453 8500987930696566078765835)
              ·
                refine ⟨12751481896044849118148753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8500987930696566078765835 12751481896044849118148753)
                ·
                  refine ⟨9563611422033636838611565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12751481896044849118148753 9563611422033636838611565)
                  ·
                    refine ⟨3586354283262613814479337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9563611422033636838611565 3586354283262613814479337)
                    ·
                      refine ⟨2689765712446960360859503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586354283262613814479337 2689765712446960360859503)
                      ·
                        rfl

theorem cell23_5238300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_5238300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238300 prefixEnd_5238300 := by exact prefixLift 5238300
  have htrace : WordTrace (prefixWord ++ tailWord_5238300) baseStart_5238300 baseEnd_5238300 := by
    simpa [prefixWord, tailWord_5238300, baseEnd_5238300] using wordTrace_append hprefix tailTrace_5238300
  have hstable : (prefixWord ++ tailWord_5238300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238300).length < 2 ^ (prefixWord ++ tailWord_5238300).sum := by decide
  have hdescent : baseEnd_5238300 < baseStart_5238300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238306 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_5238306 : Nat := 118140960795 + 5238306 * 2 ^ 59
def prefixEnd_5238306 : Nat := 4983230072969 + 3 ^ 40 * 5238306 * 2
def baseEnd_5238306 : Nat := 896589597776962445794825

theorem tailTrace_5238306 : CollatzResearch.WordTrace tailWord_5238306 prefixEnd_5238306 896589597776962445794825 := by
  unfold tailWord_5238306
  simp only [CollatzResearch.WordTrace]
  refine ⟨47764178940129867071165693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127371143840346312189775181 47764178940129867071165693)
  ·
    refine ⟨17911567102548700151687135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47764178940129867071165693 17911567102548700151687135)
    ·
      refine ⟨26867350653823050227530703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17911567102548700151687135 26867350653823050227530703)
      ·
        refine ⟨40301025980734575341296055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26867350653823050227530703 40301025980734575341296055)
        ·
          refine ⟨60451538971101863011944083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40301025980734575341296055 60451538971101863011944083)
          ·
            refine ⟨90677308456652794517916125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60451538971101863011944083 90677308456652794517916125)
            ·
              refine ⟨34003990671244797944218547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90677308456652794517916125 34003990671244797944218547)
              ·
                refine ⟨51005986006867196916327821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34003990671244797944218547 51005986006867196916327821)
                ·
                  refine ⟨19127244752575198843622933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51005986006867196916327821 19127244752575198843622933)
                  ·
                    refine ⟨896589597776962445794825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19127244752575198843622933 896589597776962445794825)
                    ·
                      rfl

theorem cell23_5238306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_5238306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238306 prefixEnd_5238306 := by exact prefixLift 5238306
  have htrace : WordTrace (prefixWord ++ tailWord_5238306) baseStart_5238306 baseEnd_5238306 := by
    simpa [prefixWord, tailWord_5238306, baseEnd_5238306] using wordTrace_append hprefix tailTrace_5238306
  have hstable : (prefixWord ++ tailWord_5238306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238306).length < 2 ^ (prefixWord ++ tailWord_5238306).sum := by decide
  have hdescent : baseEnd_5238306 < baseStart_5238306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238323 : List Nat := [1, 1, 1, 2, 4, 3, 1, 4, 2, 4]
def baseStart_5238323 : Nat := 118140960795 + 5238323 * 2 ^ 59
def prefixEnd_5238323 : Nat := 4983230072969 + 3 ^ 40 * 5238323 * 2
def baseEnd_5238323 : Nat := 896592507500671256957299

theorem tailTrace_5238323 : CollatzResearch.WordTrace tailWord_5238323 prefixEnd_5238323 896592507500671256957299 := by
  unfold tailWord_5238323
  simp only [CollatzResearch.WordTrace]
  refine ⟨191057335801457880188031623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127371557200971920125354415 191057335801457880188031623)
  ·
    refine ⟨286586003702186820282047435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191057335801457880188031623 286586003702186820282047435)
    ·
      refine ⟨429879005553280230423071153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286586003702186820282047435 429879005553280230423071153)
      ·
        refine ⟨322409254164960172817303365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429879005553280230423071153 322409254164960172817303365)
        ·
          refine ⟨60451735155930032403244381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 322409254164960172817303365 60451735155930032403244381)
          ·
            refine ⟨22669400683473762151216643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60451735155930032403244381 22669400683473762151216643)
            ·
              refine ⟨34004101025210643226824965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22669400683473762151216643 34004101025210643226824965)
              ·
                refine ⟨6375768942226995605029681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34004101025210643226824965 6375768942226995605029681)
                ·
                  refine ⟨4781826706670246703772261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6375768942226995605029681 4781826706670246703772261)
                  ·
                    refine ⟨896592507500671256957299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4781826706670246703772261 896592507500671256957299)
                    ·
                      rfl

theorem cell23_5238323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 4].length) (baseStart_5238323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238323 prefixEnd_5238323 := by exact prefixLift 5238323
  have htrace : WordTrace (prefixWord ++ tailWord_5238323) baseStart_5238323 baseEnd_5238323 := by
    simpa [prefixWord, tailWord_5238323, baseEnd_5238323] using wordTrace_append hprefix tailTrace_5238323
  have hstable : (prefixWord ++ tailWord_5238323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238323).length < 2 ^ (prefixWord ++ tailWord_5238323).sum := by decide
  have hdescent : baseEnd_5238323 < baseStart_5238323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238330 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2]
def baseStart_5238330 : Nat := 118140960795 + 5238330 * 2 ^ 59
def prefixEnd_5238330 : Nat := 4983230072969 + 3 ^ 40 * 5238330 * 2
def baseEnd_5238330 : Nat := 2689781116866595243484365

theorem tailTrace_5238330 : CollatzResearch.WordTrace tailWord_5238330 prefixEnd_5238330 2689781116866595243484365 := by
  unfold tailWord_5238330
  simp only [CollatzResearch.WordTrace]
  refine ⟨47764397778108130095884111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127371727408288346922357629 47764397778108130095884111)
  ·
    refine ⟨71646596667162195143826167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47764397778108130095884111 71646596667162195143826167)
    ·
      refine ⟨107469895000743292715739251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71646596667162195143826167 107469895000743292715739251)
      ·
        refine ⟨161204842501114939073608877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107469895000743292715739251 161204842501114939073608877)
        ·
          refine ⟨60451815937918102152603329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161204842501114939073608877 60451815937918102152603329)
          ·
            refine ⟨45338861953438576614452497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60451815937918102152603329 45338861953438576614452497)
            ·
              refine ⟨34004146465078932460839373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45338861953438576614452497 34004146465078932460839373)
              ·
                refine ⟨12751554924404599672814765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34004146465078932460839373 12751554924404599672814765)
                ·
                  refine ⟨4781833096651724877305537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12751554924404599672814765 4781833096651724877305537)
                  ·
                    refine ⟨3586374822488793657979153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4781833096651724877305537 3586374822488793657979153)
                    ·
                      refine ⟨2689781116866595243484365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586374822488793657979153 2689781116866595243484365)
                      ·
                        rfl

theorem cell23_5238330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2].length) (baseStart_5238330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238330 prefixEnd_5238330 := by exact prefixLift 5238330
  have htrace : WordTrace (prefixWord ++ tailWord_5238330) baseStart_5238330 baseEnd_5238330 := by
    simpa [prefixWord, tailWord_5238330, baseEnd_5238330] using wordTrace_append hprefix tailTrace_5238330
  have hstable : (prefixWord ++ tailWord_5238330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238330).length < 2 ^ (prefixWord ++ tailWord_5238330).sum := by decide
  have hdescent : baseEnd_5238330 < baseStart_5238330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238358 : List Nat := [5, 2, 2, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_5238358 : Nat := 118140960795 + 5238358 * 2 ^ 59
def prefixEnd_5238358 : Nat := 4983230072969 + 3 ^ 40 * 5238358 * 2
def baseEnd_5238358 : Nat := 2689795494324921133934237

theorem tailTrace_5238358 : CollatzResearch.WordTrace tailWord_5238358 prefixEnd_5238358 2689795494324921133934237 := by
  unfold tailWord_5238358
  simp only [CollatzResearch.WordTrace]
  refine ⟨11941163272270692572847233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127372408237554054110370485 11941163272270692572847233)
  ·
    refine ⟨8955872454203019429635425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11941163272270692572847233 8955872454203019429635425)
    ·
      refine ⟨6716904340652264572226569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8955872454203019429635425 6716904340652264572226569)
      ·
        refine ⟨5037678255489198429169927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6716904340652264572226569 5037678255489198429169927)
        ·
          refine ⟨7556517383233797643754891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5037678255489198429169927 7556517383233797643754891)
          ·
            refine ⟨11334776074850696465632337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7556517383233797643754891 11334776074850696465632337)
            ·
              refine ⟨8501082056138022349224253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11334776074850696465632337 8501082056138022349224253)
              ·
                refine ⟨3187905771051758380959095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8501082056138022349224253 3187905771051758380959095)
                ·
                  refine ⟨4781858656577637571438643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3187905771051758380959095 4781858656577637571438643)
                  ·
                    refine ⟨7172787984866456357157965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4781858656577637571438643 7172787984866456357157965)
                    ·
                      refine ⟨2689795494324921133934237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7172787984866456357157965 2689795494324921133934237)
                      ·
                        rfl

theorem cell23_5238358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_5238358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238358 prefixEnd_5238358 := by exact prefixLift 5238358
  have htrace : WordTrace (prefixWord ++ tailWord_5238358) baseStart_5238358 baseEnd_5238358 := by
    simpa [prefixWord, tailWord_5238358, baseEnd_5238358] using wordTrace_append hprefix tailTrace_5238358
  have hstable : (prefixWord ++ tailWord_5238358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238358).length < 2 ^ (prefixWord ++ tailWord_5238358).sum := by decide
  have hdescent : baseEnd_5238358 < baseStart_5238358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238364 : List Nat := [2, 2, 4, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_5238364 : Nat := 118140960795 + 5238364 * 2 ^ 59
def prefixEnd_5238364 : Nat := 4983230072969 + 3 ^ 40 * 5238364 * 2
def baseEnd_5238364 : Nat := 2689798575208848110459209

theorem tailTrace_5238364 : CollatzResearch.WordTrace tailWord_5238364 prefixEnd_5238364 2689798575208848110459209 := by
  unfold tailWord_5238364
  simp only [CollatzResearch.WordTrace]
  refine ⟨95529415597154672095137073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127372554129539562793516097 95529415597154672095137073)
  ·
    refine ⟨71647061697866004071352805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95529415597154672095137073 71647061697866004071352805)
    ·
      refine ⟨13433824068349875763378651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71647061697866004071352805 13433824068349875763378651)
      ·
        refine ⟨20150736102524813645067977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13433824068349875763378651 20150736102524813645067977)
        ·
          refine ⟨15113052076893610233800983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20150736102524813645067977 15113052076893610233800983)
          ·
            refine ⟨22669578115340415350701475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15113052076893610233800983 22669578115340415350701475)
            ·
              refine ⟨34004367173010623026052213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22669578115340415350701475 34004367173010623026052213)
              ·
                refine ⟨3187909422469745908692395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34004367173010623026052213 3187909422469745908692395)
                ·
                  refine ⟨4781864133704618863038593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3187909422469745908692395 4781864133704618863038593)
                  ·
                    refine ⟨3586398100278464147278945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4781864133704618863038593 3586398100278464147278945)
                    ·
                      refine ⟨2689798575208848110459209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586398100278464147278945 2689798575208848110459209)
                      ·
                        rfl

theorem cell23_5238364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_5238364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238364 prefixEnd_5238364 := by exact prefixLift 5238364
  have htrace : WordTrace (prefixWord ++ tailWord_5238364) baseStart_5238364 baseEnd_5238364 := by
    simpa [prefixWord, tailWord_5238364, baseEnd_5238364] using wordTrace_append hprefix tailTrace_5238364
  have hstable : (prefixWord ++ tailWord_5238364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238364).length < 2 ^ (prefixWord ++ tailWord_5238364).sum := by decide
  have hdescent : baseEnd_5238364 < baseStart_5238364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238407 : List Nat := [1, 1, 4, 2, 1, 4, 2, 2, 1, 3, 2]
def baseStart_5238407 : Nat := 118140960795 + 5238407 * 2 ^ 59
def prefixEnd_5238407 : Nat := 4983230072969 + 3 ^ 40 * 5238407 * 2
def baseEnd_5238407 : Nat := 2689820654876991442221511

theorem tailTrace_5238407 : CollatzResearch.WordTrace tailWord_5238407 prefixEnd_5238407 2689820654876991442221511 := by
  unfold tailWord_5238407
  simp only [CollatzResearch.WordTrace]
  refine ⟨191060399533153562534089475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127373599688769041689392983 191060399533153562534089475)
  ·
    refine ⟨286590599299730343801134213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191060399533153562534089475 286590599299730343801134213)
    ·
      refine ⟨53735737368699439462712665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286590599299730343801134213 53735737368699439462712665)
      ·
        refine ⟨40301803026524579597034499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53735737368699439462712665 40301803026524579597034499)
        ·
          refine ⟨60452704539786869395551749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40301803026524579597034499 60452704539786869395551749)
          ·
            refine ⟨11334882101210038011665953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60452704539786869395551749 11334882101210038011665953)
            ·
              refine ⟨8501161575907528508749465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11334882101210038011665953 8501161575907528508749465)
              ·
                refine ⟨6375871181930646381562099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8501161575907528508749465 6375871181930646381562099)
                ·
                  refine ⟨9563806772895969572343149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6375871181930646381562099 9563806772895969572343149)
                  ·
                    refine ⟨3586427539835988589628681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9563806772895969572343149 3586427539835988589628681)
                    ·
                      refine ⟨2689820654876991442221511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586427539835988589628681 2689820654876991442221511)
                      ·
                        rfl

theorem cell23_5238407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_5238407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238407 prefixEnd_5238407 := by exact prefixLift 5238407
  have htrace : WordTrace (prefixWord ++ tailWord_5238407) baseStart_5238407 baseEnd_5238407 := by
    simpa [prefixWord, tailWord_5238407, baseEnd_5238407] using wordTrace_append hprefix tailTrace_5238407
  have hstable : (prefixWord ++ tailWord_5238407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238407).length < 2 ^ (prefixWord ++ tailWord_5238407).sum := by decide
  have hdescent : baseEnd_5238407 < baseStart_5238407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238416 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 4]
def baseStart_5238416 : Nat := 118140960795 + 5238416 * 2 ^ 59
def prefixEnd_5238416 : Nat := 4983230072969 + 3 ^ 40 * 5238416 * 2
def baseEnd_5238416 : Nat := 2689825276202881907008969

theorem tailTrace_5238416 : CollatzResearch.WordTrace tailWord_5238416 prefixEnd_5238416 2689825276202881907008969 := by
  unfold tailWord_5238416
  simp only [CollatzResearch.WordTrace]
  refine ⟨95530363895060478535583551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127373818526747304714111401 95530363895060478535583551)
  ·
    refine ⟨143295545842590717803375327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95530363895060478535583551 143295545842590717803375327)
    ·
      refine ⟨214943318763886076705062991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143295545842590717803375327 214943318763886076705062991)
      ·
        refine ⟨322414978145829115057594487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214943318763886076705062991 322414978145829115057594487)
        ·
          refine ⟨483622467218743672586391731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322414978145829115057594487 483622467218743672586391731)
          ·
            refine ⟨725433700828115508879587597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483622467218743672586391731 725433700828115508879587597)
            ·
              refine ⟨272037637810543315829845349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 725433700828115508879587597 272037637810543315829845349)
              ·
                refine ⟨51007057089476871718096003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272037637810543315829845349 51007057089476871718096003)
                ·
                  refine ⟨76510585634215307577144005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51007057089476871718096003 76510585634215307577144005)
                  ·
                    refine ⟨14345734806415370170714501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76510585634215307577144005 14345734806415370170714501)
                    ·
                      refine ⟨2689825276202881907008969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14345734806415370170714501 2689825276202881907008969)
                      ·
                        rfl

theorem cell23_5238416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_5238416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238416 prefixEnd_5238416 := by exact prefixLift 5238416
  have htrace : WordTrace (prefixWord ++ tailWord_5238416) baseStart_5238416 baseEnd_5238416 := by
    simpa [prefixWord, tailWord_5238416, baseEnd_5238416] using wordTrace_append hprefix tailTrace_5238416
  have hstable : (prefixWord ++ tailWord_5238416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238416).length < 2 ^ (prefixWord ++ tailWord_5238416).sum := by decide
  have hdescent : baseEnd_5238416 < baseStart_5238416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238423 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_5238423 : Nat := 118140960795 + 5238423 * 2 ^ 59
def prefixEnd_5238423 : Nat := 4983230072969 + 3 ^ 40 * 5238423 * 2
def baseEnd_5238423 : Nat := 2689828870567463379621437

theorem tailTrace_5238423 : CollatzResearch.WordTrace tailWord_5238423 prefixEnd_5238423 2689828870567463379621437 := by
  unfold tailWord_5238423
  simp only [CollatzResearch.WordTrace]
  refine ⟨191060983101095597266671923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127373988734063731511114615 191060983101095597266671923)
  ·
    refine ⟨286591474651643395900007885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191060983101095597266671923 286591474651643395900007885)
    ·
      refine ⟨107471802994366273462502957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286591474651643395900007885 107471802994366273462502957)
      ·
        refine ⟨40301926122887352548438609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107471802994366273462502957 40301926122887352548438609)
        ·
          refine ⟨30226444592165514411328957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40301926122887352548438609 30226444592165514411328957)
          ·
            refine ⟨11334916722062067904248359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30226444592165514411328957 11334916722062067904248359)
            ·
              refine ⟨17002375083093101856372539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11334916722062067904248359 17002375083093101856372539)
              ·
                refine ⟨25503562624639652784558809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17002375083093101856372539 25503562624639652784558809)
                ·
                  refine ⟨19127671968479739588419107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25503562624639652784558809 19127671968479739588419107)
                  ·
                    refine ⟨28691507952719609382628661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19127671968479739588419107 28691507952719609382628661)
                    ·
                      refine ⟨2689828870567463379621437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28691507952719609382628661 2689828870567463379621437)
                      ·
                        rfl

theorem cell23_5238423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_5238423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238423 prefixEnd_5238423 := by exact prefixLift 5238423
  have htrace : WordTrace (prefixWord ++ tailWord_5238423) baseStart_5238423 baseEnd_5238423 := by
    simpa [prefixWord, tailWord_5238423, baseEnd_5238423] using wordTrace_append hprefix tailTrace_5238423
  have hstable : (prefixWord ++ tailWord_5238423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238423).length < 2 ^ (prefixWord ++ tailWord_5238423).sum := by decide
  have hdescent : baseEnd_5238423 < baseStart_5238423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238456 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 3, 7]
def baseStart_5238456 : Nat := 118140960795 + 5238456 * 2 ^ 59
def prefixEnd_5238456 : Nat := 4983230072969 + 3 ^ 40 * 5238456 * 2
def baseEnd_5238456 : Nat := 896615271809687250169595

theorem tailTrace_5238456 : CollatzResearch.WordTrace tailWord_5238456 prefixEnd_5238456 896615271809687250169595 := by
  unfold tailWord_5238456
  simp only [CollatzResearch.WordTrace]
  refine ⟨95531093354988021951311611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127374791139984029268415481 95531093354988021951311611)
  ·
    refine ⟨143296640032482032926967417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95531093354988021951311611 143296640032482032926967417)
    ·
      refine ⟨107472480024361524695225563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143296640032482032926967417 107472480024361524695225563)
      ·
        refine ⟨161208720036542287042838345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107472480024361524695225563 161208720036542287042838345)
        ·
          refine ⟨120906540027406715282128759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161208720036542287042838345 120906540027406715282128759)
          ·
            refine ⟨181359810041110072923193139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120906540027406715282128759 181359810041110072923193139)
            ·
              refine ⟨272039715061665109384789709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181359810041110072923193139 272039715061665109384789709)
              ·
                refine ⟨102014893148124416019296141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272039715061665109384789709 102014893148124416019296141)
                ·
                  refine ⟨38255584930546656007236053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102014893148124416019296141 38255584930546656007236053)
                  ·
                    refine ⟨896615271809687250169595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38255584930546656007236053 896615271809687250169595)
                    ·
                      rfl

theorem cell23_5238456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_5238456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238456 prefixEnd_5238456 := by exact prefixLift 5238456
  have htrace : WordTrace (prefixWord ++ tailWord_5238456) baseStart_5238456 baseEnd_5238456 := by
    simpa [prefixWord, tailWord_5238456, baseEnd_5238456] using wordTrace_append hprefix tailTrace_5238456
  have hstable : (prefixWord ++ tailWord_5238456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238456).length < 2 ^ (prefixWord ++ tailWord_5238456).sum := by decide
  have hdescent : baseEnd_5238456 < baseStart_5238456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238563 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 5, 5]
def baseStart_5238563 : Nat := 118140960795 + 5238563 * 2 ^ 59
def prefixEnd_5238563 : Nat := 4983230072969 + 3 ^ 40 * 5238563 * 2
def baseEnd_5238563 : Nat := 896633585953030943956931

theorem tailTrace_5238563 : CollatzResearch.WordTrace tailWord_5238563 prefixEnd_5238563 896633585953030943956931 := by
  unfold tailWord_5238563
  simp only [CollatzResearch.WordTrace]
  refine ⟨191066089320588401176768343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127377392880392267451178895 191066089320588401176768343)
  ·
    refine ⟨286599133980882601765152515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191066089320588401176768343 286599133980882601765152515)
    ·
      refine ⟨429898700971323902647728773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286599133980882601765152515 429898700971323902647728773)
      ·
        refine ⟨80606006432123231746449145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 429898700971323902647728773 80606006432123231746449145)
        ·
          refine ⟨60454504824092423809836859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80606006432123231746449145 60454504824092423809836859)
          ·
            refine ⟨90681757236138635714755289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60454504824092423809836859 90681757236138635714755289)
            ·
              refine ⟨68011317927103976786066467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90681757236138635714755289 68011317927103976786066467)
              ·
                refine ⟨102016976890655965179099701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68011317927103976786066467 102016976890655965179099701)
                ·
                  refine ⟨9564091583498996735540597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102016976890655965179099701 9564091583498996735540597)
                  ·
                    refine ⟨896633585953030943956931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9564091583498996735540597 896633585953030943956931)
                    ·
                      rfl

theorem cell23_5238563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 5].length) (baseStart_5238563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238563 prefixEnd_5238563 := by exact prefixLift 5238563
  have htrace : WordTrace (prefixWord ++ tailWord_5238563) baseStart_5238563 baseEnd_5238563 := by
    simpa [prefixWord, tailWord_5238563, baseEnd_5238563] using wordTrace_append hprefix tailTrace_5238563
  have hstable : (prefixWord ++ tailWord_5238563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238563).length < 2 ^ (prefixWord ++ tailWord_5238563).sum := by decide
  have hdescent : baseEnd_5238563 < baseStart_5238563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238577 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 3, 1, 3]
def baseStart_5238577 : Nat := 118140960795 + 5238577 * 2 ^ 59
def prefixEnd_5238577 : Nat := 4983230072969 + 3 ^ 40 * 5238577 * 2
def baseEnd_5238577 : Nat := 2689907946588255777095729

theorem tailTrace_5238577 : CollatzResearch.WordTrace tailWord_5238577 prefixEnd_5238577 2689907946588255777095729 := by
  unfold tailWord_5238577
  simp only [CollatzResearch.WordTrace]
  refine ⟨191066599942537681567777985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127377733295025121045185323 191066599942537681567777985)
  ·
    refine ⟨143299949956903261175833489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191066599942537681567777985 143299949956903261175833489)
    ·
      refine ⟨107474962467677445881875117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143299949956903261175833489 107474962467677445881875117)
      ·
        refine ⟨40303110925379042205703169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107474962467677445881875117 40303110925379042205703169)
        ·
          refine ⟨30227333194034281654277377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40303110925379042205703169 30227333194034281654277377)
          ·
            refine ⟨22670499895525711240708033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30227333194034281654277377 22670499895525711240708033)
            ·
              refine ⟨17002874921644283430531025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22670499895525711240708033 17002874921644283430531025)
              ·
                refine ⟨12752156191233212572898269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17002874921644283430531025 12752156191233212572898269)
                ·
                  refine ⟨4782058571712454714836851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12752156191233212572898269 4782058571712454714836851)
                  ·
                    refine ⟨7173087857568682072255277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4782058571712454714836851 7173087857568682072255277)
                    ·
                      refine ⟨2689907946588255777095729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7173087857568682072255277 2689907946588255777095729)
                      ·
                        rfl

theorem cell23_5238577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_5238577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238577 prefixEnd_5238577 := by exact prefixLift 5238577
  have htrace : WordTrace (prefixWord ++ tailWord_5238577) baseStart_5238577 baseEnd_5238577 := by
    simpa [prefixWord, tailWord_5238577, baseEnd_5238577] using wordTrace_append hprefix tailTrace_5238577
  have hstable : (prefixWord ++ tailWord_5238577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238577).length < 2 ^ (prefixWord ++ tailWord_5238577).sum := by decide
  have hdescent : baseEnd_5238577 < baseStart_5238577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238604 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 2, 3, 2]
def baseStart_5238604 : Nat := 118140960795 + 5238604 * 2 ^ 59
def prefixEnd_5238604 : Nat := 4983230072969 + 3 ^ 40 * 5238604 * 2
def baseEnd_5238604 : Nat := 2689921810565927171458105

theorem tailTrace_5238604 : CollatzResearch.WordTrace tailWord_5238604 prefixEnd_5238604 2689921810565927171458105 := by
  unfold tailWord_5238604
  simp only [CollatzResearch.WordTrace]
  refine ⟨95533792356719932589505433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127378389808959910119340577 95533792356719932589505433)
  ·
    refine ⟨71650344267539949442129075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95533792356719932589505433 71650344267539949442129075)
    ·
      refine ⟨107475516401309924163193613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71650344267539949442129075 107475516401309924163193613)
      ·
        refine ⟨40303318650491221561197605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107475516401309924163193613 40303318650491221561197605)
        ·
          refine ⟨7556872246967104042724551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40303318650491221561197605 7556872246967104042724551)
          ·
            refine ⟨11335308370450656064086827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7556872246967104042724551 11335308370450656064086827)
            ·
              refine ⟨17002962555675984096130241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11335308370450656064086827 17002962555675984096130241)
              ·
                refine ⟨12752221916756988072097681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17002962555675984096130241 12752221916756988072097681)
                ·
                  refine ⟨9564166437567741054073261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12752221916756988072097681 9564166437567741054073261)
                  ·
                    refine ⟨3586562414087902895277473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9564166437567741054073261 3586562414087902895277473)
                    ·
                      refine ⟨2689921810565927171458105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586562414087902895277473 2689921810565927171458105)
                      ·
                        rfl

theorem cell23_5238604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_5238604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238604 prefixEnd_5238604 := by exact prefixLift 5238604
  have htrace : WordTrace (prefixWord ++ tailWord_5238604) baseStart_5238604 baseEnd_5238604 := by
    simpa [prefixWord, tailWord_5238604, baseEnd_5238604] using wordTrace_append hprefix tailTrace_5238604
  have hstable : (prefixWord ++ tailWord_5238604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238604).length < 2 ^ (prefixWord ++ tailWord_5238604).sum := by decide
  have hdescent : baseEnd_5238604 < baseStart_5238604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238623 : List Nat := [1, 1, 2, 3, 1, 4, 1, 10]
def baseStart_5238623 : Nat := 118140960795 + 5238623 * 2 ^ 59
def prefixEnd_5238623 : Nat := 4983230072969 + 3 ^ 40 * 5238623 * 2
def baseEnd_5238623 : Nat := 99627095062902318411871

theorem tailTrace_5238623 : CollatzResearch.WordTrace tailWord_5238623 prefixEnd_5238623 99627095062902318411871 := by
  unfold tailWord_5238623
  simp only [CollatzResearch.WordTrace]
  refine ⟨191068277700371031423952523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127378851800247354282635015 191068277700371031423952523)
  ·
    refine ⟨286602416550556547135928785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191068277700371031423952523 286602416550556547135928785)
    ·
      refine ⟨214951812412917410351946589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286602416550556547135928785 214951812412917410351946589)
      ·
        refine ⟨80606929654844028881979971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214951812412917410351946589 80606929654844028881979971)
        ·
          refine ⟨120910394482266043322969957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80606929654844028881979971 120910394482266043322969957)
          ·
            refine ⟨22670698965424883123056867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120910394482266043322969957 22670698965424883123056867)
            ·
              refine ⟨34006048448137324684585301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22670698965424883123056867 34006048448137324684585301)
              ·
                refine ⟨99627095062902318411871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34006048448137324684585301 99627095062902318411871)
                ·
                  rfl

theorem cell23_5238623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 10].length) (baseStart_5238623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238623 prefixEnd_5238623 := by exact prefixLift 5238623
  have htrace : WordTrace (prefixWord ++ tailWord_5238623) baseStart_5238623 baseEnd_5238623 := by
    simpa [prefixWord, tailWord_5238623, baseEnd_5238623] using wordTrace_append hprefix tailTrace_5238623
  have hstable : (prefixWord ++ tailWord_5238623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238623).length < 2 ^ (prefixWord ++ tailWord_5238623).sum := by decide
  have hdescent : baseEnd_5238623 < baseStart_5238623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238634 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_5238634 : Nat := 118140960795 + 5238634 * 2 ^ 59
def prefixEnd_5238634 : Nat := 4983230072969 + 3 ^ 40 * 5238634 * 2
def baseEnd_5238634 : Nat := 2689937214985562054082967

theorem tailTrace_5238634 : CollatzResearch.WordTrace tailWord_5238634 prefixEnd_5238634 2689937214985562054082967 := by
  unfold tailWord_5238634
  simp only [CollatzResearch.WordTrace]
  refine ⟨47767169725832795075650739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127379119268887453535068637 47767169725832795075650739)
  ·
    refine ⟨71650754588749192613476109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47767169725832795075650739 71650754588749192613476109)
    ·
      refine ⟨26869032970780947230053541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71650754588749192613476109 26869032970780947230053541)
      ·
        refine ⟨5037943682021427605635039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26869032970780947230053541 5037943682021427605635039)
        ·
          refine ⟨7556915523032141408452559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5037943682021427605635039 7556915523032141408452559)
          ·
            refine ⟨11335373284548212112678839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7556915523032141408452559 11335373284548212112678839)
            ·
              refine ⟨17003059926822318169018259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11335373284548212112678839 17003059926822318169018259)
              ·
                refine ⟨25504589890233477253527389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17003059926822318169018259 25504589890233477253527389)
                ·
                  refine ⟨9564221208837553970072771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25504589890233477253527389 9564221208837553970072771)
                  ·
                    refine ⟨14346331813256330955109157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9564221208837553970072771 14346331813256330955109157)
                    ·
                      refine ⟨2689937214985562054082967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14346331813256330955109157 2689937214985562054082967)
                      ·
                        rfl

theorem cell23_5238634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_5238634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238634 prefixEnd_5238634 := by exact prefixLift 5238634
  have htrace : WordTrace (prefixWord ++ tailWord_5238634) baseStart_5238634 baseEnd_5238634 := by
    simpa [prefixWord, tailWord_5238634, baseEnd_5238634] using wordTrace_append hprefix tailTrace_5238634
  have hstable : (prefixWord ++ tailWord_5238634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238634).length < 2 ^ (prefixWord ++ tailWord_5238634).sum := by decide
  have hdescent : baseEnd_5238634 < baseStart_5238634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238650 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3]
def baseStart_5238650 : Nat := 118140960795 + 5238650 * 2 ^ 59
def prefixEnd_5238650 : Nat := 4983230072969 + 3 ^ 40 * 5238650 * 2
def baseEnd_5238650 : Nat := 2689945430676033991482893

theorem tailTrace_5238650 : CollatzResearch.WordTrace tailWord_5238650 prefixEnd_5238650 2689945430676033991482893 := by
  unfold tailWord_5238650
  simp only [CollatzResearch.WordTrace]
  refine ⟨47767315617818303758796351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127379508314182143356790269 47767315617818303758796351)
  ·
    refine ⟨71650973426727455638194527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47767315617818303758796351 71650973426727455638194527)
    ·
      refine ⟨107476460140091183457291791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71650973426727455638194527 107476460140091183457291791)
      ·
        refine ⟨161214690210136775185937687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107476460140091183457291791 161214690210136775185937687)
        ·
          refine ⟨241822035315205162778906531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161214690210136775185937687 241822035315205162778906531)
          ·
            refine ⟨362733052972807744168359797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241822035315205162778906531 362733052972807744168359797)
            ·
              refine ⟨34006223716200726015783731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 362733052972807744168359797 34006223716200726015783731)
              ·
                refine ⟨51009335574301089023675597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34006223716200726015783731 51009335574301089023675597)
                ·
                  refine ⟨19128500840362908383878349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51009335574301089023675597 19128500840362908383878349)
                  ·
                    refine ⟨7173187815136090643954381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19128500840362908383878349 7173187815136090643954381)
                    ·
                      refine ⟨2689945430676033991482893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7173187815136090643954381 2689945430676033991482893)
                      ·
                        rfl

theorem cell23_5238650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_5238650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238650 prefixEnd_5238650 := by exact prefixLift 5238650
  have htrace : WordTrace (prefixWord ++ tailWord_5238650) baseStart_5238650 baseEnd_5238650 := by
    simpa [prefixWord, tailWord_5238650, baseEnd_5238650] using wordTrace_append hprefix tailTrace_5238650
  have hstable : (prefixWord ++ tailWord_5238650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238650).length < 2 ^ (prefixWord ++ tailWord_5238650).sum := by decide
  have hdescent : baseEnd_5238650 < baseStart_5238650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238654 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_5238654 : Nat := 118140960795 + 5238654 * 2 ^ 59
def prefixEnd_5238654 : Nat := 4983230072969 + 3 ^ 40 * 5238654 * 2
def baseEnd_5238654 : Nat := 2689947484598651975832875

theorem tailTrace_5238654 : CollatzResearch.WordTrace tailWord_5238654 prefixEnd_5238654 2689947484598651975832875 := by
  unfold tailWord_5238654
  simp only [CollatzResearch.WordTrace]
  refine ⟨23883676045407340464791377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127379605575505815812220677 23883676045407340464791377)
  ·
    refine ⟨17912757034055505348593533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23883676045407340464791377 17912757034055505348593533)
    ·
      refine ⟨6717283887770814505722575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17912757034055505348593533 6717283887770814505722575)
      ·
        refine ⟨10075925831656221758583863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6717283887770814505722575 10075925831656221758583863)
        ·
          refine ⟨15113888747484332637875795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10075925831656221758583863 15113888747484332637875795)
          ·
            refine ⟨22670833121226498956813693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15113888747484332637875795 22670833121226498956813693)
            ·
              refine ⟨8501562420459937108805135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22670833121226498956813693 8501562420459937108805135)
              ·
                refine ⟨12752343630689905663207703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8501562420459937108805135 12752343630689905663207703)
                ·
                  refine ⟨19128515446034858494811555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12752343630689905663207703 19128515446034858494811555)
                  ·
                    refine ⟨28692773169052287742217333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19128515446034858494811555 28692773169052287742217333)
                    ·
                      refine ⟨2689947484598651975832875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28692773169052287742217333 2689947484598651975832875)
                      ·
                        rfl

theorem cell23_5238654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_5238654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238654 prefixEnd_5238654 := by exact prefixLift 5238654
  have htrace : WordTrace (prefixWord ++ tailWord_5238654) baseStart_5238654 baseEnd_5238654 := by
    simpa [prefixWord, tailWord_5238654, baseEnd_5238654] using wordTrace_append hprefix tailTrace_5238654
  have hstable : (prefixWord ++ tailWord_5238654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238654).length < 2 ^ (prefixWord ++ tailWord_5238654).sum := by decide
  have hdescent : baseEnd_5238654 < baseStart_5238654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238657 : List Nat := [1, 2, 4, 4, 2, 10]
def baseStart_5238657 : Nat := 118140960795 + 5238657 * 2 ^ 59
def prefixEnd_5238657 : Nat := 4983230072969 + 3 ^ 40 * 5238657 * 2
def baseEnd_5238657 : Nat := 11069749074241215901627

theorem tailTrace_5238657 : CollatzResearch.WordTrace tailWord_5238657 prefixEnd_5238657 11069749074241215901627 := by
  unfold tailWord_5238657
  simp only [CollatzResearch.WordTrace]
  refine ⟨191069517782247855230690225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127379678521498570153793483 191069517782247855230690225)
  ·
    refine ⟨143302138336685891423017669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191069517782247855230690225 143302138336685891423017669)
    ·
      refine ⟨26869150938128604641815813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143302138336685891423017669 26869150938128604641815813)
      ·
        refine ⟨5037965800899113370340465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26869150938128604641815813 5037965800899113370340465)
        ·
          refine ⟨3778474350674335027755349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5037965800899113370340465 3778474350674335027755349)
          ·
            refine ⟨11069749074241215901627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3778474350674335027755349 11069749074241215901627)
            ·
              rfl

theorem cell23_5238657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 10].length) (baseStart_5238657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238657 prefixEnd_5238657 := by exact prefixLift 5238657
  have htrace : WordTrace (prefixWord ++ tailWord_5238657) baseStart_5238657 baseEnd_5238657 := by
    simpa [prefixWord, tailWord_5238657, baseEnd_5238657] using wordTrace_append hprefix tailTrace_5238657
  have hstable : (prefixWord ++ tailWord_5238657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238657).length < 2 ^ (prefixWord ++ tailWord_5238657).sum := by decide
  have hdescent : baseEnd_5238657 < baseStart_5238657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238677 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 5, 3, 2]
def baseStart_5238677 : Nat := 118140960795 + 5238677 * 2 ^ 59
def prefixEnd_5238677 : Nat := 4983230072969 + 3 ^ 40 * 5238677 * 2
def baseEnd_5238677 : Nat := 2689959294653705385845269

theorem tailTrace_5238677 : CollatzResearch.WordTrace tailWord_5238677 prefixEnd_5238677 2689959294653705385845269 := by
  unfold tailWord_5238677
  simp only [CollatzResearch.WordTrace]
  refine ⟨191070247242175398646418285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127380164828116932430945523 191070247242175398646418285)
  ·
    refine ⟨71651342715815774492406857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191070247242175398646418285 71651342715815774492406857)
    ·
      refine ⟨53738507036861830869305143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71651342715815774492406857 53738507036861830869305143)
      ·
        refine ⟨80607760555292746303957715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53738507036861830869305143 80607760555292746303957715)
        ·
          refine ⟨120911640832939119455936573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80607760555292746303957715 120911640832939119455936573)
          ·
            refine ⟨45341865312352169795976215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120911640832939119455936573 45341865312352169795976215)
            ·
              refine ⟨68012797968528254693964323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45341865312352169795976215 68012797968528254693964323)
              ·
                refine ⟨102019196952792382040946485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68012797968528254693964323 102019196952792382040946485)
                ·
                  refine ⟨9564299714324285816338733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102019196952792382040946485 9564299714324285816338733)
                  ·
                    refine ⟨3586612392871607181127025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9564299714324285816338733 3586612392871607181127025)
                    ·
                      refine ⟨2689959294653705385845269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586612392871607181127025 2689959294653705385845269)
                      ·
                        rfl

theorem cell23_5238677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_5238677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238677 prefixEnd_5238677 := by exact prefixLift 5238677
  have htrace : WordTrace (prefixWord ++ tailWord_5238677) baseStart_5238677 baseEnd_5238677 := by
    simpa [prefixWord, tailWord_5238677, baseEnd_5238677] using wordTrace_append hprefix tailTrace_5238677
  have hstable : (prefixWord ++ tailWord_5238677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238677).length < 2 ^ (prefixWord ++ tailWord_5238677).sum := by decide
  have hdescent : baseEnd_5238677 < baseStart_5238677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238684 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_5238684 : Nat := 118140960795 + 5238684 * 2 ^ 59
def prefixEnd_5238684 : Nat := 4983230072969 + 3 ^ 40 * 5238684 * 2
def baseEnd_5238684 : Nat := 2689962889018286858457737

theorem tailTrace_5238684 : CollatzResearch.WordTrace tailWord_5238684 prefixEnd_5238684 2689962889018286858457737 := by
  unfold tailWord_5238684
  simp only [CollatzResearch.WordTrace]
  refine ⟨95535251276575019420961553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127380335035433359227948737 95535251276575019420961553)
  ·
    refine ⟨71651438457431264565721165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95535251276575019420961553 71651438457431264565721165)
    ·
      refine ⟨26869289421536724212145437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71651438457431264565721165 26869289421536724212145437)
      ·
        refine ⟨10075983533076271579554539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26869289421536724212145437 10075983533076271579554539)
        ·
          refine ⟨15113975299614407369331809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10075983533076271579554539 15113975299614407369331809)
          ·
            refine ⟨11335481474710805526998857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15113975299614407369331809 11335481474710805526998857)
            ·
              refine ⟨8501611106033104145249143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11335481474710805526998857 8501611106033104145249143)
              ·
                refine ⟨12752416659049656217873715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8501611106033104145249143 12752416659049656217873715)
                ·
                  refine ⟨19128624988574484326810573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12752416659049656217873715 19128624988574484326810573)
                  ·
                    refine ⟨7173234370715431622553965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19128624988574484326810573 7173234370715431622553965)
                    ·
                      refine ⟨2689962889018286858457737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7173234370715431622553965 2689962889018286858457737)
                      ·
                        rfl

theorem cell23_5238684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_5238684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238684 prefixEnd_5238684 := by exact prefixLift 5238684
  have htrace : WordTrace (prefixWord ++ tailWord_5238684) baseStart_5238684 baseEnd_5238684 := by
    simpa [prefixWord, tailWord_5238684, baseEnd_5238684] using wordTrace_append hprefix tailTrace_5238684
  have hstable : (prefixWord ++ tailWord_5238684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238684).length < 2 ^ (prefixWord ++ tailWord_5238684).sum := by decide
  have hdescent : baseEnd_5238684 < baseStart_5238684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238702 : List Nat := [4, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_5238702 : Nat := 118140960795 + 5238702 * 2 ^ 59
def prefixEnd_5238702 : Nat := 4983230072969 + 3 ^ 40 * 5238702 * 2
def baseEnd_5238702 : Nat := 2689972131670067788032655

theorem tailTrace_5238702 : CollatzResearch.WordTrace tailWord_5238702 prefixEnd_5238702 2689972131670067788032655 := by
  unfold tailWord_5238702
  simp only [CollatzResearch.WordTrace]
  refine ⟨23883894883385603489509795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127380772711389885277385573 23883894883385603489509795)
  ·
    refine ⟨35825842325078405234264693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23883894883385603489509795 35825842325078405234264693)
    ·
      refine ⟨3358672717976100490712315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35825842325078405234264693 3358672717976100490712315)
      ·
        refine ⟨5038009076964150736068473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3358672717976100490712315 5038009076964150736068473)
        ·
          refine ⟨3778506807723113052051355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5038009076964150736068473 3778506807723113052051355)
          ·
            refine ⟨5667760211584669578077033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3778506807723113052051355 5667760211584669578077033)
            ·
              refine ⟨4250820158688502183557775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5667760211584669578077033 4250820158688502183557775)
              ·
                refine ⟨6376230238032753275336663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4250820158688502183557775 6376230238032753275336663)
                ·
                  refine ⟨9564345357049129913004995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6376230238032753275336663 9564345357049129913004995)
                  ·
                    refine ⟨14346518035573694869507493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9564345357049129913004995 14346518035573694869507493)
                    ·
                      refine ⟨2689972131670067788032655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14346518035573694869507493 2689972131670067788032655)
                      ·
                        rfl

theorem cell23_5238702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_5238702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238702 prefixEnd_5238702 := by exact prefixLift 5238702
  have htrace : WordTrace (prefixWord ++ tailWord_5238702) baseStart_5238702 baseEnd_5238702 := by
    simpa [prefixWord, tailWord_5238702, baseEnd_5238702] using wordTrace_append hprefix tailTrace_5238702
  have hstable : (prefixWord ++ tailWord_5238702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238702).length < 2 ^ (prefixWord ++ tailWord_5238702).sum := by decide
  have hdescent : baseEnd_5238702 < baseStart_5238702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238707 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 1, 4, 2]
def baseStart_5238707 : Nat := 118140960795 + 5238707 * 2 ^ 59
def prefixEnd_5238707 : Nat := 4983230072969 + 3 ^ 40 * 5238707 * 2
def baseEnd_5238707 : Nat := 2689974699073340268470131

theorem tailTrace_5238707 : CollatzResearch.WordTrace tailWord_5238707 prefixEnd_5238707 2689974699073340268470131 := by
  unfold tailWord_5238707
  simp only [CollatzResearch.WordTrace]
  refine ⟨191071341432066713770010375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127380894288044475846673583 191071341432066713770010375)
  ·
    refine ⟨286607012148100070655015563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191071341432066713770010375 286607012148100070655015563)
    ·
      refine ⟨429910518222150105982523345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286607012148100070655015563 429910518222150105982523345)
      ·
        refine ⟨322432888666612579486892509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429910518222150105982523345 322432888666612579486892509)
        ·
          refine ⟨120912333249979717307584691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322432888666612579486892509 120912333249979717307584691)
          ·
            refine ⟨181368499874969575961377037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120912333249979717307584691 181368499874969575961377037)
            ·
              refine ⟨68013187453113590985516389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181368499874969575961377037 68013187453113590985516389)
              ·
                refine ⟨12752472647458798309784323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68013187453113590985516389 12752472647458798309784323)
                ·
                  refine ⟨19128708971188197464676485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12752472647458798309784323 19128708971188197464676485)
                  ·
                    refine ⟨3586632932097787024626841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19128708971188197464676485 3586632932097787024626841)
                    ·
                      refine ⟨2689974699073340268470131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586632932097787024626841 2689974699073340268470131)
                      ·
                        rfl

theorem cell23_5238707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 4, 2].length) (baseStart_5238707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238707 prefixEnd_5238707 := by exact prefixLift 5238707
  have htrace : WordTrace (prefixWord ++ tailWord_5238707) baseStart_5238707 baseEnd_5238707 := by
    simpa [prefixWord, tailWord_5238707, baseEnd_5238707] using wordTrace_append hprefix tailTrace_5238707
  have hstable : (prefixWord ++ tailWord_5238707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238707).length < 2 ^ (prefixWord ++ tailWord_5238707).sum := by decide
  have hdescent : baseEnd_5238707 < baseStart_5238707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238720 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 4]
def baseStart_5238720 : Nat := 118140960795 + 5238720 * 2 ^ 59
def prefixEnd_5238720 : Nat := 4983230072969 + 3 ^ 40 * 5238720 * 2
def baseEnd_5238720 : Nat := 2689981374321848717607571

theorem tailTrace_5238720 : CollatzResearch.WordTrace tailWord_5238720 prefixEnd_5238720 2689981374321848717607571 := by
  unfold tailWord_5238720
  simp only [CollatzResearch.WordTrace]
  refine ⟨95535907790509808495116807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127381210387346411326822409 95535907790509808495116807)
  ·
    refine ⟨143303861685764712742675211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95535907790509808495116807 143303861685764712742675211)
    ·
      refine ⟨214955792528647069114012817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143303861685764712742675211 214955792528647069114012817)
      ·
        refine ⟨161216844396485301835509613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214955792528647069114012817 161216844396485301835509613)
        ·
          refine ⟨60456316648681988188316105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161216844396485301835509613 60456316648681988188316105)
          ·
            refine ⟨45342237486511491141237079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60456316648681988188316105 45342237486511491141237079)
            ·
              refine ⟨68013356229767236711855619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45342237486511491141237079 68013356229767236711855619)
              ·
                refine ⟨102020034344650855067783429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68013356229767236711855619 102020034344650855067783429)
                ·
                  refine ⟨19128756439622035325209393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102020034344650855067783429 19128756439622035325209393)
                  ·
                    refine ⟨14346567329716526493907045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19128756439622035325209393 14346567329716526493907045)
                    ·
                      refine ⟨2689981374321848717607571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14346567329716526493907045 2689981374321848717607571)
                      ·
                        rfl

theorem cell23_5238720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_5238720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238720 prefixEnd_5238720 := by exact prefixLift 5238720
  have htrace : WordTrace (prefixWord ++ tailWord_5238720) baseStart_5238720 baseEnd_5238720 := by
    simpa [prefixWord, tailWord_5238720, baseEnd_5238720] using wordTrace_append hprefix tailTrace_5238720
  have hstable : (prefixWord ++ tailWord_5238720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238720).length < 2 ^ (prefixWord ++ tailWord_5238720).sum := by decide
  have hdescent : baseEnd_5238720 < baseStart_5238720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238730 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 7]
def baseStart_5238730 : Nat := 118140960795 + 5238730 * 2 ^ 59
def prefixEnd_5238730 : Nat := 4983230072969 + 3 ^ 40 * 5238730 * 2
def baseEnd_5238730 : Nat := 298887389903154853164725

theorem tailTrace_5238730 : CollatzResearch.WordTrace tailWord_5238730 prefixEnd_5238730 298887389903154853164725 := by
  unfold tailWord_5238730
  simp only [CollatzResearch.WordTrace]
  refine ⟨47768045077745847174524411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127381453540655592465398429 47768045077745847174524411)
  ·
    refine ⟨71652067616618770761786617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47768045077745847174524411 71652067616618770761786617)
    ·
      refine ⟨53739050712464078071339963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71652067616618770761786617 53739050712464078071339963)
      ·
        refine ⟨80608576068696117107009945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53739050712464078071339963 80608576068696117107009945)
        ·
          refine ⟨60456432051522087830257459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80608576068696117107009945 60456432051522087830257459)
          ·
            refine ⟨90684648077283131745386189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60456432051522087830257459 90684648077283131745386189)
            ·
              refine ⟨34006743028981174404519821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90684648077283131745386189 34006743028981174404519821)
              ·
                refine ⟨12752528635867940401694933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34006743028981174404519821 12752528635867940401694933)
                ·
                  refine ⟨298887389903154853164725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12752528635867940401694933 298887389903154853164725)
                  ·
                    rfl

theorem cell23_5238730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_5238730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238730 prefixEnd_5238730 := by exact prefixLift 5238730
  have htrace : WordTrace (prefixWord ++ tailWord_5238730) baseStart_5238730 baseEnd_5238730 := by
    simpa [prefixWord, tailWord_5238730, baseEnd_5238730] using wordTrace_append hprefix tailTrace_5238730
  have hstable : (prefixWord ++ tailWord_5238730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238730).length < 2 ^ (prefixWord ++ tailWord_5238730).sum := by decide
  have hdescent : baseEnd_5238730 < baseStart_5238730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238741 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 1, 4, 2]
def baseStart_5238741 : Nat := 118140960795 + 5238741 * 2 ^ 59
def prefixEnd_5238741 : Nat := 4983230072969 + 3 ^ 40 * 5238741 * 2
def baseEnd_5238741 : Nat := 2689992157415593135444975

theorem tailTrace_5238741 : CollatzResearch.WordTrace tailWord_5238741 prefixEnd_5238741 2689992157415593135444975 := by
  unfold tailWord_5238741
  simp only [CollatzResearch.WordTrace]
  refine ⟨191072581513943537576748077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127381721009295691717832051 191072581513943537576748077)
  ·
    refine ⟨71652218067728826591280529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191072581513943537576748077 71652218067728826591280529)
    ·
      refine ⟨53739163550796619943460397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71652218067728826591280529 53739163550796619943460397)
      ·
        refine ⟨20152186331548732478797649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53739163550796619943460397 20152186331548732478797649)
        ·
          refine ⟨15114139748661549359098237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20152186331548732478797649 15114139748661549359098237)
          ·
            refine ⟨5667802405748081009661839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15114139748661549359098237 5667802405748081009661839)
            ·
              refine ⟨8501703608622121514492759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5667802405748081009661839 8501703608622121514492759)
              ·
                refine ⟨12752555412933182271739139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8501703608622121514492759 12752555412933182271739139)
                ·
                  refine ⟨19128833119399773407608709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12752555412933182271739139 19128833119399773407608709)
                  ·
                    refine ⟨3586656209887457513926633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19128833119399773407608709 3586656209887457513926633)
                    ·
                      refine ⟨2689992157415593135444975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586656209887457513926633 2689992157415593135444975)
                      ·
                        rfl

theorem cell23_5238741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_5238741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238741 prefixEnd_5238741 := by exact prefixLift 5238741
  have htrace : WordTrace (prefixWord ++ tailWord_5238741) baseStart_5238741 baseEnd_5238741 := by
    simpa [prefixWord, tailWord_5238741, baseEnd_5238741] using wordTrace_append hprefix tailTrace_5238741
  have hstable : (prefixWord ++ tailWord_5238741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238741).length < 2 ^ (prefixWord ++ tailWord_5238741).sum := by decide
  have hdescent : baseEnd_5238741 < baseStart_5238741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238777 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 2, 5]
def baseStart_5238777 : Nat := 118140960795 + 5238777 * 2 ^ 59
def prefixEnd_5238777 : Nat := 4983230072969 + 3 ^ 40 * 5238777 * 2
def baseEnd_5238777 : Nat := 896670214239718331531603

theorem tailTrace_5238777 : CollatzResearch.WordTrace tailWord_5238777 prefixEnd_5238777 896670214239718331531603 := by
  unfold tailWord_5238777
  simp only [CollatzResearch.WordTrace]
  refine ⟨191073894541813115725058585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127382596361208743816705723 191073894541813115725058585)
  ·
    refine ⟨143305420906359836793793939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191073894541813115725058585 143305420906359836793793939)
    ·
      refine ⟨214958131359539755190690909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143305420906359836793793939 214958131359539755190690909)
      ·
        refine ⟨80609299259827408196509091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214958131359539755190690909 80609299259827408196509091)
        ·
          refine ⟨120913948889741112294763637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80609299259827408196509091 120913948889741112294763637)
          ·
            refine ⟨11335682708413229277634091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120913948889741112294763637 11335682708413229277634091)
            ·
              refine ⟨17003524062619843916451137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11335682708413229277634091 17003524062619843916451137)
              ·
                refine ⟨12752643046964882937338353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17003524062619843916451137 12752643046964882937338353)
                ·
                  refine ⟨9564482285223662203003765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12752643046964882937338353 9564482285223662203003765)
                  ·
                    refine ⟨896670214239718331531603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9564482285223662203003765 896670214239718331531603)
                    ·
                      rfl

theorem cell23_5238777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 5].length) (baseStart_5238777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238777 prefixEnd_5238777 := by exact prefixLift 5238777
  have htrace : WordTrace (prefixWord ++ tailWord_5238777) baseStart_5238777 baseEnd_5238777 := by
    simpa [prefixWord, tailWord_5238777, baseEnd_5238777] using wordTrace_append hprefix tailTrace_5238777
  have hstable : (prefixWord ++ tailWord_5238777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238777).length < 2 ^ (prefixWord ++ tailWord_5238777).sum := by decide
  have hdescent : baseEnd_5238777 < baseStart_5238777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238834 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_5238834 : Nat := 118140960795 + 5238834 * 2 ^ 59
def prefixEnd_5238834 : Nat := 4983230072969 + 3 ^ 40 * 5238834 * 2
def baseEnd_5238834 : Nat := 2690039911116461271582047

theorem tailTrace_5238834 : CollatzResearch.WordTrace tailWord_5238834 prefixEnd_5238834 2690039911116461271582047 := by
  unfold tailWord_5238834
  simp only [CollatzResearch.WordTrace]
  refine ⟨47768993375651653614970889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127383982335071076306589037 47768993375651653614970889)
  ·
    refine ⟨35826745031738740211228167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47768993375651653614970889 35826745031738740211228167)
    ·
      refine ⟨53740117547608110316842251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35826745031738740211228167 53740117547608110316842251)
      ·
        refine ⟨80610176321412165475263377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53740117547608110316842251 80610176321412165475263377)
        ·
          refine ⟨60457632241059124106447533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80610176321412165475263377 60457632241059124106447533)
          ·
            refine ⟨22671612090397171539917825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60457632241059124106447533 22671612090397171539917825)
            ·
              refine ⟨17003709067797878654938369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22671612090397171539917825 17003709067797878654938369)
              ·
                refine ⟨12752781800848408991203777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17003709067797878654938369 12752781800848408991203777)
                ·
                  refine ⟨9564586350636306743402833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12752781800848408991203777 9564586350636306743402833)
                  ·
                    refine ⟨7173439762977230057552125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9564586350636306743402833 7173439762977230057552125)
                    ·
                      refine ⟨2690039911116461271582047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7173439762977230057552125 2690039911116461271582047)
                      ·
                        rfl

theorem cell23_5238834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_5238834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238834 prefixEnd_5238834 := by exact prefixLift 5238834
  have htrace : WordTrace (prefixWord ++ tailWord_5238834) baseStart_5238834 baseEnd_5238834 := by
    simpa [prefixWord, tailWord_5238834, baseEnd_5238834] using wordTrace_append hprefix tailTrace_5238834
  have hstable : (prefixWord ++ tailWord_5238834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238834).length < 2 ^ (prefixWord ++ tailWord_5238834).sum := by decide
  have hdescent : baseEnd_5238834 < baseStart_5238834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238837 : List Nat := [1, 3, 3, 1, 1, 1, 3, 4, 6]
def baseStart_5238837 : Nat := 118140960795 + 5238837 * 2 ^ 59
def prefixEnd_5238837 : Nat := 4983230072969 + 3 ^ 40 * 5238837 * 2
def baseEnd_5238837 : Nat := 298893494617602751093837

theorem tailTrace_5238837 : CollatzResearch.WordTrace tailWord_5238837 prefixEnd_5238837 298893494617602751093837 := by
  unfold tailWord_5238837
  simp only [CollatzResearch.WordTrace]
  refine ⟨191076082921595745972242765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127384055281063830648161843 191076082921595745972242765)
  ·
    refine ⟨71653531095598404739591037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191076082921595745972242765 71653531095598404739591037)
    ·
      refine ⟨26870074160849401777346639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71653531095598404739591037 26870074160849401777346639)
      ·
        refine ⟨40305111241274102666019959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26870074160849401777346639 40305111241274102666019959)
        ·
          refine ⟨60457666861911153999029939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40305111241274102666019959 60457666861911153999029939)
          ·
            refine ⟨90686500292866730998544909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60457666861911153999029939 90686500292866730998544909)
            ·
              refine ⟨34007437609825024124454341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90686500292866730998544909 34007437609825024124454341)
              ·
                refine ⟨6376394551842192023335189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34007437609825024124454341 6376394551842192023335189)
                ·
                  refine ⟨298893494617602751093837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6376394551842192023335189 298893494617602751093837)
                  ·
                    rfl

theorem cell23_5238837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_5238837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238837 prefixEnd_5238837 := by exact prefixLift 5238837
  have htrace : WordTrace (prefixWord ++ tailWord_5238837) baseStart_5238837 baseEnd_5238837 := by
    simpa [prefixWord, tailWord_5238837, baseEnd_5238837] using wordTrace_append hprefix tailTrace_5238837
  have hstable : (prefixWord ++ tailWord_5238837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238837).length < 2 ^ (prefixWord ++ tailWord_5238837).sum := by decide
  have hdescent : baseEnd_5238837 < baseStart_5238837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238874 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2]
def baseStart_5238874 : Nat := 118140960795 + 5238874 * 2 ^ 59
def prefixEnd_5238874 : Nat := 4983230072969 + 3 ^ 40 * 5238874 * 2
def baseEnd_5238874 : Nat := 2690060450342641115081863

theorem tailTrace_5238874 : CollatzResearch.WordTrace tailWord_5238874 prefixEnd_5238874 2690060450342641115081863 := by
  unfold tailWord_5238874
  simp only [CollatzResearch.WordTrace]
  refine ⟨47769358105615425322834919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127384954948307800860893117 47769358105615425322834919)
  ·
    refine ⟨71654037158423137984252379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47769358105615425322834919 71654037158423137984252379)
    ·
      refine ⟨107481055737634706976378569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71654037158423137984252379 107481055737634706976378569)
      ·
        refine ⟨80610791803226030232283927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107481055737634706976378569 80610791803226030232283927)
        ·
          refine ⟨120916187704839045348425891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80610791803226030232283927 120916187704839045348425891)
          ·
            refine ⟨181374281557258568022638837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120916187704839045348425891 181374281557258568022638837)
            ·
              refine ⟨17003838895992990752122391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181374281557258568022638837 17003838895992990752122391)
              ·
                refine ⟨25505758343989486128183587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17003838895992990752122391 25505758343989486128183587)
                ·
                  refine ⟨38258637515984229192275381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25505758343989486128183587 38258637515984229192275381)
                  ·
                    refine ⟨3586747267123521486775817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38258637515984229192275381 3586747267123521486775817)
                    ·
                      refine ⟨2690060450342641115081863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586747267123521486775817 2690060450342641115081863)
                      ·
                        rfl

theorem cell23_5238874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_5238874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238874 prefixEnd_5238874 := by exact prefixLift 5238874
  have htrace : WordTrace (prefixWord ++ tailWord_5238874) baseStart_5238874 baseEnd_5238874 := by
    simpa [prefixWord, tailWord_5238874, baseEnd_5238874] using wordTrace_append hprefix tailTrace_5238874
  have hstable : (prefixWord ++ tailWord_5238874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238874).length < 2 ^ (prefixWord ++ tailWord_5238874).sum := by decide
  have hdescent : baseEnd_5238874 < baseStart_5238874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238898 : List Nat := [3, 2, 1, 2, 2, 2, 2, 4, 1, 1, 3]
def baseStart_5238898 : Nat := 118140960795 + 5238898 * 2 ^ 59
def prefixEnd_5238898 : Nat := 4983230072969 + 3 ^ 40 * 5238898 * 2
def baseEnd_5238898 : Nat := 2690072773878349021181753

theorem tailTrace_5238898 : CollatzResearch.WordTrace tailWord_5238898 prefixEnd_5238898 2690072773878349021181753 := by
  unfold tailWord_5238898
  simp only [CollatzResearch.WordTrace]
  refine ⟨47769576943593688347553337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127385538516249835593475565 47769576943593688347553337)
  ·
    refine ⟨35827182707695266260665003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47769576943593688347553337 35827182707695266260665003)
    ·
      refine ⟨53740774061542899390997505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35827182707695266260665003 53740774061542899390997505)
      ·
        refine ⟨40305580546157174543248129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53740774061542899390997505 40305580546157174543248129)
        ·
          refine ⟨30229185409617880907436097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40305580546157174543248129 30229185409617880907436097)
          ·
            refine ⟨22671889057213410680577073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30229185409617880907436097 22671889057213410680577073)
            ·
              refine ⟨17003916792910058010432805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22671889057213410680577073 17003916792910058010432805)
              ·
                refine ⟨3188234398670635876956151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17003916792910058010432805 3188234398670635876956151)
                ·
                  refine ⟨4782351598005953815434227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3188234398670635876956151 4782351598005953815434227)
                  ·
                    refine ⟨7173527397008930723151341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4782351598005953815434227 7173527397008930723151341)
                    ·
                      refine ⟨2690072773878349021181753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7173527397008930723151341 2690072773878349021181753)
                      ·
                        rfl

theorem cell23_5238898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_5238898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238898 prefixEnd_5238898 := by exact prefixLift 5238898
  have htrace : WordTrace (prefixWord ++ tailWord_5238898) baseStart_5238898 baseEnd_5238898 := by
    simpa [prefixWord, tailWord_5238898, baseEnd_5238898] using wordTrace_append hprefix tailTrace_5238898
  have hstable : (prefixWord ++ tailWord_5238898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238898).length < 2 ^ (prefixWord ++ tailWord_5238898).sum := by decide
  have hdescent : baseEnd_5238898 < baseStart_5238898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238921 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 3, 2, 2]
def baseStart_5238921 : Nat := 118140960795 + 5238921 * 2 ^ 59
def prefixEnd_5238921 : Nat := 4983230072969 + 3 ^ 40 * 5238921 * 2
def baseEnd_5238921 : Nat := 2690084583933402431194147

theorem tailTrace_5238921 : CollatzResearch.WordTrace tailWord_5238921 prefixEnd_5238921 2690084583933402431194147 := by
  unfold tailWord_5238921
  simp only [CollatzResearch.WordTrace]
  refine ⟨191079146653291428318300617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127386097768860952212200411 191079146653291428318300617)
  ·
    refine ⟨143309359989968571238725463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191079146653291428318300617 143309359989968571238725463)
    ·
      refine ⟨214964039984952856858088195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143309359989968571238725463 214964039984952856858088195)
      ·
        refine ⟨322446059977429285287132293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214964039984952856858088195 322446059977429285287132293)
        ·
          refine ⟨60458636245767990991337305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 322446059977429285287132293 60458636245767990991337305)
          ·
            refine ⟨45343977184325993243502979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60458636245767990991337305 45343977184325993243502979)
            ·
              refine ⟨68015965776488989865254469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45343977184325993243502979 68015965776488989865254469)
              ·
                refine ⟨12752993583091685599735213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68015965776488989865254469 12752993583091685599735213)
                ·
                  refine ⟨4782372593659382099900705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12752993583091685599735213 4782372593659382099900705)
                  ·
                    refine ⟨3586779445244536574925529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4782372593659382099900705 3586779445244536574925529)
                    ·
                      refine ⟨2690084583933402431194147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586779445244536574925529 2690084583933402431194147)
                      ·
                        rfl

theorem cell23_5238921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 2, 2].length) (baseStart_5238921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238921 prefixEnd_5238921 := by exact prefixLift 5238921
  have htrace : WordTrace (prefixWord ++ tailWord_5238921) baseStart_5238921 baseEnd_5238921 := by
    simpa [prefixWord, tailWord_5238921, baseEnd_5238921] using wordTrace_append hprefix tailTrace_5238921
  have hstable : (prefixWord ++ tailWord_5238921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238921).length < 2 ^ (prefixWord ++ tailWord_5238921).sum := by decide
  have hdescent : baseEnd_5238921 < baseStart_5238921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238941 : List Nat := [1, 4, 2, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_5238941 : Nat := 118140960795 + 5238941 * 2 ^ 59
def prefixEnd_5238941 : Nat := 4983230072969 + 3 ^ 40 * 5238941 * 2
def baseEnd_5238941 : Nat := 2690094853546492352944055

theorem tailTrace_5238941 : CollatzResearch.WordTrace tailWord_5238941 prefixEnd_5238941 2690094853546492352944055 := by
  unfold tailWord_5238941
  simp only [CollatzResearch.WordTrace]
  refine ⟨191079876113218971734028677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127386584075479314489352451 191079876113218971734028677)
  ·
    refine ⟨35827476771228557200130377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191079876113218971734028677 35827476771228557200130377)
    ·
      refine ⟨26870607578421417900097783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35827476771228557200130377 26870607578421417900097783)
      ·
        refine ⟨40305911367632126850146675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26870607578421417900097783 40305911367632126850146675)
        ·
          refine ⟨60458867051448190275220013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40305911367632126850146675 60458867051448190275220013)
          ·
            refine ⟨22672075144293071353207505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60458867051448190275220013 22672075144293071353207505)
            ·
              refine ⟨17004056358219803514905629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22672075144293071353207505 17004056358219803514905629)
              ·
                refine ⟨6376521134332426318089611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17004056358219803514905629 6376521134332426318089611)
                ·
                  refine ⟨9564781701498639477134417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6376521134332426318089611 9564781701498639477134417)
                  ·
                    refine ⟨7173586276123979607850813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9564781701498639477134417 7173586276123979607850813)
                    ·
                      refine ⟨2690094853546492352944055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7173586276123979607850813 2690094853546492352944055)
                      ·
                        rfl

theorem cell23_5238941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_5238941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238941 prefixEnd_5238941 := by exact prefixLift 5238941
  have htrace : WordTrace (prefixWord ++ tailWord_5238941) baseStart_5238941 baseEnd_5238941 := by
    simpa [prefixWord, tailWord_5238941, baseEnd_5238941] using wordTrace_append hprefix tailTrace_5238941
  have hstable : (prefixWord ++ tailWord_5238941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238941).length < 2 ^ (prefixWord ++ tailWord_5238941).sum := by decide
  have hdescent : baseEnd_5238941 < baseStart_5238941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238971 : List Nat := [1, 1, 1, 1, 1, 2, 7, 3, 2, 1, 3]
def baseStart_5238971 : Nat := 118140960795 + 5238971 * 2 ^ 59
def prefixEnd_5238971 : Nat := 4983230072969 + 3 ^ 40 * 5238971 * 2
def baseEnd_5238971 : Nat := 2690110257966127235568917

theorem tailTrace_5238971 : CollatzResearch.WordTrace tailWord_5238971 prefixEnd_5238971 2690110257966127235568917 := by
  unfold tailWord_5238971
  simp only [CollatzResearch.WordTrace]
  refine ⟨191080970303110286857620767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127387313535406857905080511 191080970303110286857620767)
  ·
    refine ⟨286621455454665430286431151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191080970303110286857620767 286621455454665430286431151)
    ·
      refine ⟨429932183181998145429646727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286621455454665430286431151 429932183181998145429646727)
      ·
        refine ⟨644898274772997218144470091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429932183181998145429646727 644898274772997218144470091)
        ·
          refine ⟨967347412159495827216705137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644898274772997218144470091 967347412159495827216705137)
          ·
            refine ⟨725510559119621870412528853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 967347412159495827216705137 725510559119621870412528853)
            ·
              refine ⟨17004153729366137587793645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 725510559119621870412528853 17004153729366137587793645)
              ·
                refine ⟨6376557648512301595422617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17004153729366137587793645 6376557648512301595422617)
                ·
                  refine ⟨4782418236384226196566963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6376557648512301595422617 4782418236384226196566963)
                  ·
                    refine ⟨7173627354576339294850445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4782418236384226196566963 7173627354576339294850445)
                    ·
                      refine ⟨2690110257966127235568917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7173627354576339294850445 2690110257966127235568917)
                      ·
                        rfl

theorem cell23_5238971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 1, 3].length) (baseStart_5238971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238971 prefixEnd_5238971 := by exact prefixLift 5238971
  have htrace : WordTrace (prefixWord ++ tailWord_5238971) baseStart_5238971 baseEnd_5238971 := by
    simpa [prefixWord, tailWord_5238971, baseEnd_5238971] using wordTrace_append hprefix tailTrace_5238971
  have hstable : (prefixWord ++ tailWord_5238971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238971).length < 2 ^ (prefixWord ++ tailWord_5238971).sum := by decide
  have hdescent : baseEnd_5238971 < baseStart_5238971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5238988 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 1, 3, 3]
def baseStart_5238988 : Nat := 118140960795 + 5238988 * 2 ^ 59
def prefixEnd_5238988 : Nat := 4983230072969 + 3 ^ 40 * 5238988 * 2
def baseEnd_5238988 : Nat := 2690118987137253669056339

theorem tailTrace_5238988 : CollatzResearch.WordTrace tailWord_5238988 prefixEnd_5238988 2690118987137253669056339 := by
  unfold tailWord_5238988
  simp only [CollatzResearch.WordTrace]
  refine ⟨95540795172024349380494809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127387726896032465840659745 95540795172024349380494809)
  ·
    refine ⟨71655596379018262035371107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95540795172024349380494809 71655596379018262035371107)
    ·
      refine ⟨107483394568527393053056661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71655596379018262035371107 107483394568527393053056661)
      ·
        refine ⟨5038284120399721549362031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107483394568527393053056661 5038284120399721549362031)
        ·
          refine ⟨7557426180599582324043047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5038284120399721549362031 7557426180599582324043047)
          ·
            refine ⟨11336139270899373486064571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7557426180599582324043047 11336139270899373486064571)
            ·
              refine ⟨17004208906349060229096857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11336139270899373486064571 17004208906349060229096857)
              ·
                refine ⟨12753156679761795171822643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17004208906349060229096857 12753156679761795171822643)
                ·
                  refine ⟨19129735019642692757733965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12753156679761795171822643 19129735019642692757733965)
                  ·
                    refine ⟨7173650632366009784150237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19129735019642692757733965 7173650632366009784150237)
                    ·
                      refine ⟨2690118987137253669056339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7173650632366009784150237 2690118987137253669056339)
                      ·
                        rfl

theorem cell23_5238988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_5238988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5238988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5238988 prefixEnd_5238988 := by exact prefixLift 5238988
  have htrace : WordTrace (prefixWord ++ tailWord_5238988) baseStart_5238988 baseEnd_5238988 := by
    simpa [prefixWord, tailWord_5238988, baseEnd_5238988] using wordTrace_append hprefix tailTrace_5238988
  have hstable : (prefixWord ++ tailWord_5238988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5238988).length < 2 ^ (prefixWord ++ tailWord_5238988).sum := by decide
  have hdescent : baseEnd_5238988 < baseStart_5238988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5238988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239005 : List Nat := [1, 4, 3, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_5239005 : Nat := 118140960795 + 5239005 * 2 ^ 59
def prefixEnd_5239005 : Nat := 4983230072969 + 3 ^ 40 * 5239005 * 2
def baseEnd_5239005 : Nat := 2690127716308380102543761

theorem tailTrace_5239005 : CollatzResearch.WordTrace tailWord_5239005 prefixEnd_5239005 2690127716308380102543761 := by
  unfold tailWord_5239005
  simp only [CollatzResearch.WordTrace]
  refine ⟨191082210384987110664358469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127388140256658073776238979 191082210384987110664358469)
  ·
    refine ⟨35827914447185083249567213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191082210384987110664358469 35827914447185083249567213)
    ·
      refine ⟨13435467917694406218587705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35827914447185083249567213 13435467917694406218587705)
      ·
        refine ⟨10076600938270804663940779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13435467917694406218587705 10076600938270804663940779)
        ·
          refine ⟨15114901407406206995911169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10076600938270804663940779 15114901407406206995911169)
          ·
            refine ⟨11336176055554655246933377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15114901407406206995911169 11336176055554655246933377)
            ·
              refine ⟨8502132041665991435200033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11336176055554655246933377 8502132041665991435200033)
              ·
                refine ⟨6376599031249493576400025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8502132041665991435200033 6376599031249493576400025)
                ·
                  refine ⟨4782449273437120182300019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6376599031249493576400025 4782449273437120182300019)
                  ·
                    refine ⟨7173673910155680273450029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4782449273437120182300019 7173673910155680273450029)
                    ·
                      refine ⟨2690127716308380102543761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7173673910155680273450029 2690127716308380102543761)
                      ·
                        rfl

theorem cell23_5239005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_5239005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239005 prefixEnd_5239005 := by exact prefixLift 5239005
  have htrace : WordTrace (prefixWord ++ tailWord_5239005) baseStart_5239005 baseEnd_5239005 := by
    simpa [prefixWord, tailWord_5239005, baseEnd_5239005] using wordTrace_append hprefix tailTrace_5239005
  have hstable : (prefixWord ++ tailWord_5239005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239005).length < 2 ^ (prefixWord ++ tailWord_5239005).sum := by decide
  have hdescent : baseEnd_5239005 < baseStart_5239005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239007 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 6]
def baseStart_5239007 : Nat := 118140960795 + 5239007 * 2 ^ 59
def prefixEnd_5239007 : Nat := 4983230072969 + 3 ^ 40 * 5239007 * 2
def baseEnd_5239007 : Nat := 2690128743269689094718751

theorem tailTrace_5239007 : CollatzResearch.WordTrace tailWord_5239007 prefixEnd_5239007 2690128743269689094718751 := by
  unfold tailWord_5239007
  simp only [CollatzResearch.WordTrace]
  refine ⟨191082283330979865005931275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127388188887319910003954183 191082283330979865005931275)
  ·
    refine ⟨286623424996469797508896913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191082283330979865005931275 286623424996469797508896913)
    ·
      refine ⟨214967568747352348131672685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286623424996469797508896913 214967568747352348131672685)
      ·
        refine ⟨80612838280257130549377257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214967568747352348131672685 80612838280257130549377257)
        ·
          refine ⟨60459628710192847912032943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80612838280257130549377257 60459628710192847912032943)
          ·
            refine ⟨90689443065289271868049415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60459628710192847912032943 90689443065289271868049415)
            ·
              refine ⟨136034164597933907802074123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90689443065289271868049415 136034164597933907802074123)
              ·
                refine ⟨204051246896900861703111185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136034164597933907802074123 204051246896900861703111185)
                ·
                  refine ⟨153038435172675646277333389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204051246896900861703111185 153038435172675646277333389)
                  ·
                    refine ⟨57389413189753367354000021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153038435172675646277333389 57389413189753367354000021)
                    ·
                      refine ⟨2690128743269689094718751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57389413189753367354000021 2690128743269689094718751)
                      ·
                        rfl

theorem cell23_5239007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_5239007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239007 prefixEnd_5239007 := by exact prefixLift 5239007
  have htrace : WordTrace (prefixWord ++ tailWord_5239007) baseStart_5239007 baseEnd_5239007 := by
    simpa [prefixWord, tailWord_5239007, baseEnd_5239007] using wordTrace_append hprefix tailTrace_5239007
  have hstable : (prefixWord ++ tailWord_5239007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239007).length < 2 ^ (prefixWord ++ tailWord_5239007).sum := by decide
  have hdescent : baseEnd_5239007 < baseStart_5239007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239021 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_5239021 : Nat := 118140960795 + 5239021 * 2 ^ 59
def prefixEnd_5239021 : Nat := 4983230072969 + 3 ^ 40 * 5239021 * 2
def baseEnd_5239021 : Nat := 896711977332950679981229

theorem tailTrace_5239021 : CollatzResearch.WordTrace tailWord_5239021 prefixEnd_5239021 896711977332950679981229 := by
  unfold tailWord_5239021
  simp only [CollatzResearch.WordTrace]
  refine ⟨191082793952929145396940917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127388529301952763597960611 191082793952929145396940917)
  ·
    refine ⟨17914011933087107380963211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191082793952929145396940917 17914011933087107380963211)
    ·
      refine ⟨26871017899630661071444817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17914011933087107380963211 26871017899630661071444817)
      ·
        refine ⟨20153263424722995803583613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26871017899630661071444817 20153263424722995803583613)
        ·
          refine ⟨7557473784271123426343855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20153263424722995803583613 7557473784271123426343855)
          ·
            refine ⟨11336210676406685139515783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7557473784271123426343855 11336210676406685139515783)
            ·
              refine ⟨17004316014610027709273675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11336210676406685139515783 17004316014610027709273675)
              ·
                refine ⟨25506474021915041563910513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17004316014610027709273675 25506474021915041563910513)
                ·
                  refine ⟨19129855516436281172932885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25506474021915041563910513 19129855516436281172932885)
                  ·
                    refine ⟨896711977332950679981229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19129855516436281172932885 896711977332950679981229)
                    ·
                      rfl

theorem cell23_5239021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_5239021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239021 prefixEnd_5239021 := by exact prefixLift 5239021
  have htrace : WordTrace (prefixWord ++ tailWord_5239021) baseStart_5239021 baseEnd_5239021 := by
    simpa [prefixWord, tailWord_5239021, baseEnd_5239021] using wordTrace_append hprefix tailTrace_5239021
  have hstable : (prefixWord ++ tailWord_5239021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239021).length < 2 ^ (prefixWord ++ tailWord_5239021).sum := by decide
  have hdescent : baseEnd_5239021 < baseStart_5239021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239034 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 7]
def baseStart_5239034 : Nat := 118140960795 + 5239034 * 2 ^ 59
def prefixEnd_5239034 : Nat := 4983230072969 + 3 ^ 40 * 5239034 * 2
def baseEnd_5239034 : Nat := 298904734138595609897903

theorem tailTrace_5239034 : CollatzResearch.WordTrace tailWord_5239034 prefixEnd_5239034 298904734138595609897903 := by
  unfold tailWord_5239034
  simp only [CollatzResearch.WordTrace]
  refine ⟨47770817025470512154291039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127388845401254699078109437 47770817025470512154291039)
  ·
    refine ⟨71656225538205768231436559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47770817025470512154291039 71656225538205768231436559)
    ·
      refine ⟨107484338307308652347154839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71656225538205768231436559 107484338307308652347154839)
      ·
        refine ⟨161226507460962978520732259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107484338307308652347154839 161226507460962978520732259)
        ·
          refine ⟨241839761191444467781098389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161226507460962978520732259 241839761191444467781098389)
          ·
            refine ⟨11336238805848959427238987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 241839761191444467781098389 11336238805848959427238987)
            ·
              refine ⟨17004358208773439140858481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11336238805848959427238987 17004358208773439140858481)
              ·
                refine ⟨12753268656580079355643861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17004358208773439140858481 12753268656580079355643861)
                ·
                  refine ⟨298904734138595609897903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12753268656580079355643861 298904734138595609897903)
                  ·
                    rfl

theorem cell23_5239034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_5239034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239034 prefixEnd_5239034 := by exact prefixLift 5239034
  have htrace : WordTrace (prefixWord ++ tailWord_5239034) baseStart_5239034 baseEnd_5239034 := by
    simpa [prefixWord, tailWord_5239034, baseEnd_5239034] using wordTrace_append hprefix tailTrace_5239034
  have hstable : (prefixWord ++ tailWord_5239034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239034).length < 2 ^ (prefixWord ++ tailWord_5239034).sum := by decide
  have hdescent : baseEnd_5239034 < baseStart_5239034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239051 : List Nat := [1, 1, 1, 1, 5, 2, 4, 3, 5]
def baseStart_5239051 : Nat := 118140960795 + 5239051 * 2 ^ 59
def prefixEnd_5239051 : Nat := 4983230072969 + 3 ^ 40 * 5239051 * 2
def baseEnd_5239051 : Nat := 298905704046498546952061

theorem tailTrace_5239051 : CollatzResearch.WordTrace tailWord_5239051 prefixEnd_5239051 298905704046498546952061 := by
  unfold tailWord_5239051
  simp only [CollatzResearch.WordTrace]
  refine ⟨191083888142820460520533007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127389258761880307013688671 191083888142820460520533007)
  ·
    refine ⟨286625832214230690780799511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191083888142820460520533007 286625832214230690780799511)
    ·
      refine ⟨429938748321346036171199267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286625832214230690780799511 429938748321346036171199267)
      ·
        refine ⟨644908122482019054256798901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429938748321346036171199267 644908122482019054256798901)
        ·
          refine ⟨60460136482689286336574897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 644908122482019054256798901 60460136482689286336574897)
          ·
            refine ⟨45345102362016964752431173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60460136482689286336574897 45345102362016964752431173)
            ·
              refine ⟨8502206692878180891080845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45345102362016964752431173 8502206692878180891080845)
              ·
                refine ⟨3188327509829317834155317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8502206692878180891080845 3188327509829317834155317)
                ·
                  refine ⟨298905704046498546952061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3188327509829317834155317 298905704046498546952061)
                  ·
                    rfl

theorem cell23_5239051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 5].length) (baseStart_5239051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239051 prefixEnd_5239051 := by exact prefixLift 5239051
  have htrace : WordTrace (prefixWord ++ tailWord_5239051) baseStart_5239051 baseEnd_5239051 := by
    simpa [prefixWord, tailWord_5239051, baseEnd_5239051] using wordTrace_append hprefix tailTrace_5239051
  have hstable : (prefixWord ++ tailWord_5239051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239051).length < 2 ^ (prefixWord ++ tailWord_5239051).sum := by decide
  have hdescent : baseEnd_5239051 < baseStart_5239051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239064 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 4, 5]
def baseStart_5239064 : Nat := 118140960795 + 5239064 * 2 ^ 59
def prefixEnd_5239064 : Nat := 4983230072969 + 3 ^ 40 * 5239064 * 2
def baseEnd_5239064 : Nat := 896719337222331790568663

theorem tailTrace_5239064 : CollatzResearch.WordTrace tailWord_5239064 prefixEnd_5239064 896719337222331790568663 := by
  unfold tailWord_5239064
  simp only [CollatzResearch.WordTrace]
  refine ⟨95542181145886681870378123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127389574861182242493837497 95542181145886681870378123)
  ·
    refine ⟨143313271718830022805567185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95542181145886681870378123 143313271718830022805567185)
    ·
      refine ⟨107484953789122517104175389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143313271718830022805567185 107484953789122517104175389)
      ·
        refine ⟨40306857670920943914065771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107484953789122517104175389 40306857670920943914065771)
        ·
          refine ⟨60460286506381415871098657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40306857670920943914065771 60460286506381415871098657)
          ·
            refine ⟨45345214879786061903323993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60460286506381415871098657 45345214879786061903323993)
            ·
              refine ⟨34008911159839546427492995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45345214879786061903323993 34008911159839546427492995)
              ·
                refine ⟨51013366739759319641239493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34008911159839546427492995 51013366739759319641239493)
                ·
                  refine ⟨9565006263704872432732405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51013366739759319641239493 9565006263704872432732405)
                  ·
                    refine ⟨896719337222331790568663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9565006263704872432732405 896719337222331790568663)
                    ·
                      rfl

theorem cell23_5239064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_5239064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239064 prefixEnd_5239064 := by exact prefixLift 5239064
  have htrace : WordTrace (prefixWord ++ tailWord_5239064) baseStart_5239064 baseEnd_5239064 := by
    simpa [prefixWord, tailWord_5239064, baseEnd_5239064] using wordTrace_append hprefix tailTrace_5239064
  have hstable : (prefixWord ++ tailWord_5239064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239064).length < 2 ^ (prefixWord ++ tailWord_5239064).sum := by decide
  have hdescent : baseEnd_5239064 < baseStart_5239064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239079 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_5239079 : Nat := 118140960795 + 5239079 * 2 ^ 59
def prefixEnd_5239079 : Nat := 4983230072969 + 3 ^ 40 * 5239079 * 2
def baseEnd_5239079 : Nat := 2690165713876812813018421

theorem tailTrace_5239079 : CollatzResearch.WordTrace tailWord_5239079 prefixEnd_5239079 2690165713876812813018421 := by
  unfold tailWord_5239079
  simp only [CollatzResearch.WordTrace]
  refine ⟨191084909386719021302552291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127389939591146014201701527 191084909386719021302552291)
  ·
    refine ⟨286627364080078531953828437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191084909386719021302552291 286627364080078531953828437)
    ·
      refine ⟨3358914422813420296333927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 286627364080078531953828437 3358914422813420296333927)
      ·
        refine ⟨5038371634220130444500891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3358914422813420296333927 5038371634220130444500891)
        ·
          refine ⟨7557557451330195666751337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5038371634220130444500891 7557557451330195666751337)
          ·
            refine ⟨5668168088497646750063503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7557557451330195666751337 5668168088497646750063503)
            ·
              refine ⟨8502252132746470125095255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5668168088497646750063503 8502252132746470125095255)
              ·
                refine ⟨12753378199119705187642883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8502252132746470125095255 12753378199119705187642883)
                ·
                  refine ⟨19130067298679557781464325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12753378199119705187642883 19130067298679557781464325)
                  ·
                    refine ⟨3586887618502417084024561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19130067298679557781464325 3586887618502417084024561)
                    ·
                      refine ⟨2690165713876812813018421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586887618502417084024561 2690165713876812813018421)
                      ·
                        rfl

theorem cell23_5239079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_5239079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239079 prefixEnd_5239079 := by exact prefixLift 5239079
  have htrace : WordTrace (prefixWord ++ tailWord_5239079) baseStart_5239079 baseEnd_5239079 := by
    simpa [prefixWord, tailWord_5239079, baseEnd_5239079] using wordTrace_append hprefix tailTrace_5239079
  have hstable : (prefixWord ++ tailWord_5239079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239079).length < 2 ^ (prefixWord ++ tailWord_5239079).sum := by decide
  have hdescent : baseEnd_5239079 < baseStart_5239079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239084 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_5239084 : Nat := 118140960795 + 5239084 * 2 ^ 59
def prefixEnd_5239084 : Nat := 4983230072969 + 3 ^ 40 * 5239084 * 2
def baseEnd_5239084 : Nat := 2690168281280085293455897

theorem tailTrace_5239084 : CollatzResearch.WordTrace tailWord_5239084 prefixEnd_5239084 2690168281280085293455897 := by
  unfold tailWord_5239084
  simp only [CollatzResearch.WordTrace]
  refine ⟨95542545875850453578242153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127390061167800604770989537 95542545875850453578242153)
  ·
    refine ⟨71656909406887840183681615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95542545875850453578242153 71656909406887840183681615)
    ·
      refine ⟨107485364110331760275522423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71656909406887840183681615 107485364110331760275522423)
      ·
        refine ⟨161228046165497640413283635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107485364110331760275522423 161228046165497640413283635)
        ·
          refine ⟨241842069248246460619925453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161228046165497640413283635 241842069248246460619925453)
          ·
            refine ⟨90690775968092422732472045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241842069248246460619925453 90690775968092422732472045)
            ·
              refine ⟨34009040988034658524677017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90690775968092422732472045 34009040988034658524677017)
              ·
                refine ⟨25506780741025993893507763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34009040988034658524677017 25506780741025993893507763)
                ·
                  refine ⟨38260171111538990840261645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25506780741025993893507763 38260171111538990840261645)
                  ·
                    refine ⟨14347564166827121565098117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38260171111538990840261645 14347564166827121565098117)
                    ·
                      refine ⟨2690168281280085293455897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14347564166827121565098117 2690168281280085293455897)
                      ·
                        rfl

theorem cell23_5239084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_5239084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239084 prefixEnd_5239084 := by exact prefixLift 5239084
  have htrace : WordTrace (prefixWord ++ tailWord_5239084) baseStart_5239084 baseEnd_5239084 := by
    simpa [prefixWord, tailWord_5239084, baseEnd_5239084] using wordTrace_append hprefix tailTrace_5239084
  have hstable : (prefixWord ++ tailWord_5239084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239084).length < 2 ^ (prefixWord ++ tailWord_5239084).sum := by decide
  have hdescent : baseEnd_5239084 < baseStart_5239084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239121 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 4, 2, 3]
def baseStart_5239121 : Nat := 118140960795 + 5239121 * 2 ^ 59
def prefixEnd_5239121 : Nat := 4983230072969 + 3 ^ 40 * 5239121 * 2
def baseEnd_5239121 : Nat := 2690187280064301648693227

theorem tailTrace_5239121 : CollatzResearch.WordTrace tailWord_5239121 prefixEnd_5239121 2690187280064301648693227 := by
  unfold tailWord_5239121
  simp only [CollatzResearch.WordTrace]
  refine ⟨191086441252566862475581217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127390960835044574983720811 191086441252566862475581217)
  ·
    refine ⟨143314830939425146856685913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191086441252566862475581217 143314830939425146856685913)
    ·
      refine ⟨107486123204568860142514435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143314830939425146856685913 107486123204568860142514435)
      ·
        refine ⟨161229184806853290213771653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107486123204568860142514435 161229184806853290213771653)
        ·
          refine ⟨30230472151284991915082185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161229184806853290213771653 30230472151284991915082185)
          ·
            refine ⟨22672854113463743936311639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30230472151284991915082185 22672854113463743936311639)
            ·
              refine ⟨34009281170195615904467459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22672854113463743936311639 34009281170195615904467459)
              ·
                refine ⟨51013921755293423856701189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34009281170195615904467459 51013921755293423856701189)
                ·
                  refine ⟨9565110329117516973131473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51013921755293423856701189 9565110329117516973131473)
                  ·
                    refine ⟨7173832746838137729848605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9565110329117516973131473 7173832746838137729848605)
                    ·
                      refine ⟨2690187280064301648693227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7173832746838137729848605 2690187280064301648693227)
                      ·
                        rfl

theorem cell23_5239121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_5239121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239121 prefixEnd_5239121 := by exact prefixLift 5239121
  have htrace : WordTrace (prefixWord ++ tailWord_5239121) baseStart_5239121 baseEnd_5239121 := by
    simpa [prefixWord, tailWord_5239121, baseEnd_5239121] using wordTrace_append hprefix tailTrace_5239121
  have hstable : (prefixWord ++ tailWord_5239121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239121).length < 2 ^ (prefixWord ++ tailWord_5239121).sum := by decide
  have hdescent : baseEnd_5239121 < baseStart_5239121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239141 : List Nat := [1, 3, 1, 3, 1, 4, 1, 3, 6]
def baseStart_5239141 : Nat := 118140960795 + 5239141 * 2 ^ 59
def prefixEnd_5239141 : Nat := 4983230072969 + 3 ^ 40 * 5239141 * 2
def baseEnd_5239141 : Nat := 298910838853043507827015

theorem tailTrace_5239141 : CollatzResearch.WordTrace tailWord_5239141 prefixEnd_5239141 298910838853043507827015 := by
  unfold tailWord_5239141
  simp only [CollatzResearch.WordTrace]
  refine ⟨191087170712494405891309277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127391447141662937260872851 191087170712494405891309277)
  ·
    refine ⟨71657689017185402209240979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191087170712494405891309277 71657689017185402209240979)
    ·
      refine ⟨107486533525778103313861469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71657689017185402209240979 107486533525778103313861469)
      ·
        refine ⟨40307450072166788742698051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107486533525778103313861469 40307450072166788742698051)
        ·
          refine ⟨60461175108250183114047077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40307450072166788742698051 60461175108250183114047077)
          ·
            refine ⟨11336470332796909333883827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60461175108250183114047077 11336470332796909333883827)
            ·
              refine ⟨17004705499195364000825741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11336470332796909333883827 17004705499195364000825741)
              ·
                refine ⟨6376764562198261500309653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17004705499195364000825741 6376764562198261500309653)
                ·
                  refine ⟨298910838853043507827015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6376764562198261500309653 298910838853043507827015)
                  ·
                    rfl

theorem cell23_5239141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_5239141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239141 prefixEnd_5239141 := by exact prefixLift 5239141
  have htrace : WordTrace (prefixWord ++ tailWord_5239141) baseStart_5239141 baseEnd_5239141 := by
    simpa [prefixWord, tailWord_5239141, baseEnd_5239141] using wordTrace_append hprefix tailTrace_5239141
  have hstable : (prefixWord ++ tailWord_5239141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239141).length < 2 ^ (prefixWord ++ tailWord_5239141).sum := by decide
  have hdescent : baseEnd_5239141 < baseStart_5239141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239164 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_5239164 : Nat := 118140960795 + 5239164 * 2 ^ 59
def prefixEnd_5239164 : Nat := 4983230072969 + 3 ^ 40 * 5239164 * 2
def baseEnd_5239164 : Nat := 2690209359732444980455529

theorem tailTrace_5239164 : CollatzResearch.WordTrace tailWord_5239164 prefixEnd_5239164 2690209359732444980455529 := by
  unfold tailWord_5239164
  simp only [CollatzResearch.WordTrace]
  refine ⟨95544004795705540409698273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127392006394274053879597697 95544004795705540409698273)
  ·
    refine ⟨71658003596779155307273705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95544004795705540409698273 71658003596779155307273705)
    ·
      refine ⟨53743502697584366480455279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71658003596779155307273705 53743502697584366480455279)
      ·
        refine ⟨80615254046376549720682919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53743502697584366480455279 80615254046376549720682919)
        ·
          refine ⟨120922881069564824581024379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80615254046376549720682919 120922881069564824581024379)
          ·
            refine ⟨181384321604347236871536569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120922881069564824581024379 181384321604347236871536569)
            ·
              refine ⟨136038241203260427653652427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181384321604347236871536569 136038241203260427653652427)
              ·
                refine ⟨204057361804890641480478641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136038241203260427653652427 204057361804890641480478641)
                ·
                  refine ⟨153043021353667981110358981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204057361804890641480478641 153043021353667981110358981)
                  ·
                    refine ⟨28695566503812746458192309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153043021353667981110358981 28695566503812746458192309)
                    ·
                      refine ⟨2690209359732444980455529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28695566503812746458192309 2690209359732444980455529)
                      ·
                        rfl

theorem cell23_5239164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_5239164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239164 prefixEnd_5239164 := by exact prefixLift 5239164
  have htrace : WordTrace (prefixWord ++ tailWord_5239164) baseStart_5239164 baseEnd_5239164 := by
    simpa [prefixWord, tailWord_5239164, baseEnd_5239164] using wordTrace_append hprefix tailTrace_5239164
  have hstable : (prefixWord ++ tailWord_5239164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239164).length < 2 ^ (prefixWord ++ tailWord_5239164).sum := by decide
  have hdescent : baseEnd_5239164 < baseStart_5239164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239191 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_5239191 : Nat := 118140960795 + 5239191 * 2 ^ 59
def prefixEnd_5239191 : Nat := 4983230072969 + 3 ^ 40 * 5239191 * 2
def baseEnd_5239191 : Nat := 2690223223710116374817905

theorem tailTrace_5239191 : CollatzResearch.WordTrace tailWord_5239191 prefixEnd_5239191 2690223223710116374817905 := by
  unfold tailWord_5239191
  simp only [CollatzResearch.WordTrace]
  refine ⟨191088994362313264430629427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127392662908208842953752951 191088994362313264430629427)
  ·
    refine ⟨286633491543469896645944141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191088994362313264430629427 286633491543469896645944141)
    ·
      refine ⟨107487559328801211242229053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286633491543469896645944141 107487559328801211242229053)
      ·
        refine ⟨40307834748300454215835895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107487559328801211242229053 40307834748300454215835895)
        ·
          refine ⟨60461752122450681323753843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40307834748300454215835895 60461752122450681323753843)
          ·
            refine ⟨90692628183676021985630765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60461752122450681323753843 90692628183676021985630765)
            ·
              refine ⟨34009735568878508244611537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90692628183676021985630765 34009735568878508244611537)
              ·
                refine ⟨25507301676658881183458653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34009735568878508244611537 25507301676658881183458653)
                ·
                  refine ⟨9565238128747080443796995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25507301676658881183458653 9565238128747080443796995)
                  ·
                    refine ⟨14347857193120620665695493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9565238128747080443796995 14347857193120620665695493)
                    ·
                      refine ⟨2690223223710116374817905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14347857193120620665695493 2690223223710116374817905)
                      ·
                        rfl

theorem cell23_5239191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_5239191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239191 prefixEnd_5239191 := by exact prefixLift 5239191
  have htrace : WordTrace (prefixWord ++ tailWord_5239191) baseStart_5239191 baseEnd_5239191 := by
    simpa [prefixWord, tailWord_5239191, baseEnd_5239191] using wordTrace_append hprefix tailTrace_5239191
  have hstable : (prefixWord ++ tailWord_5239191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239191).length < 2 ^ (prefixWord ++ tailWord_5239191).sum := by decide
  have hdescent : baseEnd_5239191 < baseStart_5239191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239225 : List Nat := [1, 2, 1, 4, 3, 1, 4, 1, 1, 1, 4]
def baseStart_5239225 : Nat := 118140960795 + 5239225 * 2 ^ 59
def prefixEnd_5239225 : Nat := 4983230072969 + 3 ^ 40 * 5239225 * 2
def baseEnd_5239225 : Nat := 2690240682052369241792749

theorem tailTrace_5239225 : CollatzResearch.WordTrace tailWord_5239225 prefixEnd_5239225 2690240682052369241792749 := by
  unfold tailWord_5239225
  simp only [CollatzResearch.WordTrace]
  refine ⟨191090234444190088237367129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127393489629460058824911419 191090234444190088237367129)
  ·
    refine ⟨143317675833142566178025347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191090234444190088237367129 143317675833142566178025347)
    ·
      refine ⟨214976513749713849267038021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143317675833142566178025347 214976513749713849267038021)
      ·
        refine ⟨40308096328071346737569629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214976513749713849267038021 40308096328071346737569629)
        ·
          refine ⟨15115536123026755026588611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40308096328071346737569629 15115536123026755026588611)
          ·
            refine ⟨22673304184540132539882917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15115536123026755026588611 22673304184540132539882917)
            ·
              refine ⟨4251244534601274851228047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22673304184540132539882917 4251244534601274851228047)
              ·
                refine ⟨6376866801901912276842071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4251244534601274851228047 6376866801901912276842071)
                ·
                  refine ⟨9565300202852868415263107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6376866801901912276842071 9565300202852868415263107)
                  ·
                    refine ⟨14347950304279302622894661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9565300202852868415263107 14347950304279302622894661)
                    ·
                      refine ⟨2690240682052369241792749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14347950304279302622894661 2690240682052369241792749)
                      ·
                        rfl

theorem cell23_5239225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_5239225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239225 prefixEnd_5239225 := by exact prefixLift 5239225
  have htrace : WordTrace (prefixWord ++ tailWord_5239225) baseStart_5239225 baseEnd_5239225 := by
    simpa [prefixWord, tailWord_5239225, baseEnd_5239225] using wordTrace_append hprefix tailTrace_5239225
  have hstable : (prefixWord ++ tailWord_5239225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239225).length < 2 ^ (prefixWord ++ tailWord_5239225).sum := by decide
  have hdescent : baseEnd_5239225 < baseStart_5239225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239241 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 3, 3, 3]
def baseStart_5239241 : Nat := 118140960795 + 5239241 * 2 ^ 59
def prefixEnd_5239241 : Nat := 4983230072969 + 3 ^ 40 * 5239241 * 2
def baseEnd_5239241 : Nat := 2690248897742841179192675

theorem tailTrace_5239241 : CollatzResearch.WordTrace tailWord_5239241 prefixEnd_5239241 2690248897742841179192675 := by
  unfold tailWord_5239241
  simp only [CollatzResearch.WordTrace]
  refine ⟨191090818012132122969949577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127393878674754748646633051 191090818012132122969949577)
  ·
    refine ⟨143318113509099092227462183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191090818012132122969949577 143318113509099092227462183)
    ·
      refine ⟨214977170263648638341193275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143318113509099092227462183 214977170263648638341193275)
      ·
        refine ⟨322465755395472957511789913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214977170263648638341193275 322465755395472957511789913)
        ·
          refine ⟨241849316546604718133842435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322465755395472957511789913 241849316546604718133842435)
          ·
            refine ⟨362773974819907077200763653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241849316546604718133842435 362773974819907077200763653)
            ·
              refine ⟨68020120278732576975143185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 362773974819907077200763653 68020120278732576975143185)
              ·
                refine ⟨51015090209049432731357389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68020120278732576975143185 51015090209049432731357389)
                ·
                  refine ⟨19130658828393537274259021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51015090209049432731357389 19130658828393537274259021)
                  ·
                    refine ⟨7173997060647576477847133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19130658828393537274259021 7173997060647576477847133)
                    ·
                      refine ⟨2690248897742841179192675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7173997060647576477847133 2690248897742841179192675)
                      ·
                        rfl

theorem cell23_5239241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 3, 3].length) (baseStart_5239241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239241 prefixEnd_5239241 := by exact prefixLift 5239241
  have htrace : WordTrace (prefixWord ++ tailWord_5239241) baseStart_5239241 baseEnd_5239241 := by
    simpa [prefixWord, tailWord_5239241, baseEnd_5239241] using wordTrace_append hprefix tailTrace_5239241
  have hstable : (prefixWord ++ tailWord_5239241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239241).length < 2 ^ (prefixWord ++ tailWord_5239241).sum := by decide
  have hdescent : baseEnd_5239241 < baseStart_5239241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239242 : List Nat := [3, 1, 2, 1, 2, 2, 1, 6, 1, 2, 2]
def baseStart_5239242 : Nat := 118140960795 + 5239242 * 2 ^ 59
def prefixEnd_5239242 : Nat := 4983230072969 + 3 ^ 40 * 5239242 * 2
def baseEnd_5239242 : Nat := 2690249411223495675280171

theorem tailTrace_5239242 : CollatzResearch.WordTrace tailWord_5239242 prefixEnd_5239242 2690249411223495675280171 := by
  unfold tailWord_5239242
  simp only [CollatzResearch.WordTrace]
  refine ⟨47772713621282125035183995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127393902990085666760490653 47772713621282125035183995)
  ·
    refine ⟨71659070431923187552775993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47772713621282125035183995 71659070431923187552775993)
    ·
      refine ⟨53744302823942390664581995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71659070431923187552775993 53744302823942390664581995)
      ·
        refine ⟨80616454235913585996872993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53744302823942390664581995 80616454235913585996872993)
        ·
          refine ⟨60462340676935189497654745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80616454235913585996872993 60462340676935189497654745)
          ·
            refine ⟨45346755507701392123241059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60462340676935189497654745 45346755507701392123241059)
            ·
              refine ⟨68020133261552088184861589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45346755507701392123241059 68020133261552088184861589)
              ·
                refine ⟨3188443746635254133665387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68020133261552088184861589 3188443746635254133665387)
                ·
                  refine ⟨4782665619952881200498081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3188443746635254133665387 4782665619952881200498081)
                  ·
                    refine ⟨3586999214964660900373561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4782665619952881200498081 3586999214964660900373561)
                    ·
                      refine ⟨2690249411223495675280171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586999214964660900373561 2690249411223495675280171)
                      ·
                        rfl

theorem cell23_5239242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_5239242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239242 prefixEnd_5239242 := by exact prefixLift 5239242
  have htrace : WordTrace (prefixWord ++ tailWord_5239242) baseStart_5239242 baseEnd_5239242 := by
    simpa [prefixWord, tailWord_5239242, baseEnd_5239242] using wordTrace_append hprefix tailTrace_5239242
  have hstable : (prefixWord ++ tailWord_5239242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239242).length < 2 ^ (prefixWord ++ tailWord_5239242).sum := by decide
  have hdescent : baseEnd_5239242 < baseStart_5239242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239252 : List Nat := [2, 4, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_5239252 : Nat := 118140960795 + 5239252 * 2 ^ 59
def prefixEnd_5239252 : Nat := 4983230072969 + 3 ^ 40 * 5239252 * 2
def baseEnd_5239252 : Nat := 896751515343346878718375

theorem tailTrace_5239252 : CollatzResearch.WordTrace tailWord_5239252 prefixEnd_5239252 896751515343346878718375 := by
  unfold tailWord_5239252
  simp only [CollatzResearch.WordTrace]
  refine ⟨95545609607546135924300005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127394146143394847899066673 95545609607546135924300005)
  ·
    refine ⟨17914801801414900485806251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95545609607546135924300005 17914801801414900485806251)
    ·
      refine ⟨26872202702122350728709377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17914801801414900485806251 26872202702122350728709377)
      ·
        refine ⟨20154152026591763046532033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26872202702122350728709377 20154152026591763046532033)
        ·
          refine ⟨15115614019943822284899025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20154152026591763046532033 15115614019943822284899025)
          ·
            refine ⟨11336710514957866713674269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15115614019943822284899025 11336710514957866713674269)
            ·
              refine ⟨4251266443109200017627851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11336710514957866713674269 4251266443109200017627851)
              ·
                refine ⟨6376899664663800026441777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4251266443109200017627851 6376899664663800026441777)
                ·
                  refine ⟨4782674748497850019831333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6376899664663800026441777 4782674748497850019831333)
                  ·
                    refine ⟨896751515343346878718375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4782674748497850019831333 896751515343346878718375)
                    ·
                      rfl

theorem cell23_5239252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_5239252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239252 prefixEnd_5239252 := by exact prefixLift 5239252
  have htrace : WordTrace (prefixWord ++ tailWord_5239252) baseStart_5239252 baseEnd_5239252 := by
    simpa [prefixWord, tailWord_5239252, baseEnd_5239252] using wordTrace_append hprefix tailTrace_5239252
  have hstable : (prefixWord ++ tailWord_5239252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239252).length < 2 ^ (prefixWord ++ tailWord_5239252).sum := by decide
  have hdescent : baseEnd_5239252 < baseStart_5239252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239271 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_5239271 : Nat := 118140960795 + 5239271 * 2 ^ 59
def prefixEnd_5239271 : Nat := 4983230072969 + 3 ^ 40 * 5239271 * 2
def baseEnd_5239271 : Nat := 2690264302162476061817537

theorem tailTrace_5239271 : CollatzResearch.WordTrace tailWord_5239271 prefixEnd_5239271 2690264302162476061817537 := by
  unfold tailWord_5239271
  simp only [CollatzResearch.WordTrace]
  refine ⟨191091912202023438093541667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127394608134682292062361111 191091912202023438093541667)
  ·
    refine ⟨286637868303035157140312501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191091912202023438093541667 286637868303035157140312501)
    ·
      refine ⟨26872300153409545981904297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 286637868303035157140312501 26872300153409545981904297)
      ·
        refine ⟨20154225115057159486428223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26872300153409545981904297 20154225115057159486428223)
        ·
          refine ⟨30231337672585739229642335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20154225115057159486428223 30231337672585739229642335)
          ·
            refine ⟨45347006508878608844463503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30231337672585739229642335 45347006508878608844463503)
            ·
              refine ⟨68020509763317913266695255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45347006508878608844463503 68020509763317913266695255)
              ·
                refine ⟨102030764644976869900042883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68020509763317913266695255 102030764644976869900042883)
                ·
                  refine ⟨153046146967465304850064325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102030764644976869900042883 153046146967465304850064325)
                  ·
                    refine ⟨28696152556399744659387061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153046146967465304850064325 28696152556399744659387061)
                    ·
                      refine ⟨2690264302162476061817537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28696152556399744659387061 2690264302162476061817537)
                      ·
                        rfl

theorem cell23_5239271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_5239271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239271 prefixEnd_5239271 := by exact prefixLift 5239271
  have htrace : WordTrace (prefixWord ++ tailWord_5239271) baseStart_5239271 baseEnd_5239271 := by
    simpa [prefixWord, tailWord_5239271, baseEnd_5239271] using wordTrace_append hprefix tailTrace_5239271
  have hstable : (prefixWord ++ tailWord_5239271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239271).length < 2 ^ (prefixWord ++ tailWord_5239271).sum := by decide
  have hdescent : baseEnd_5239271 < baseStart_5239271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239366 : List Nat := [6, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_5239366 : Nat := 118140960795 + 5239366 * 2 ^ 59
def prefixEnd_5239366 : Nat := 4983230072969 + 3 ^ 40 * 5239366 * 2
def baseEnd_5239366 : Nat := 2690313082824653190129601

theorem tailTrace_5239366 : CollatzResearch.WordTrace tailWord_5239366 prefixEnd_5239366 2690313082824653190129601 := by
  unfold tailWord_5239366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5971730535521227166195311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127396918091119512878833301 5971730535521227166195311)
  ·
    refine ⟨8957595803281840749292967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5971730535521227166195311 8957595803281840749292967)
    ·
      refine ⟨13436393704922761123939451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8957595803281840749292967 13436393704922761123939451)
      ·
        refine ⟨20154590557384141685909177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13436393704922761123939451 20154590557384141685909177)
        ·
          refine ⟨15115942918038106264431883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20154590557384141685909177 15115942918038106264431883)
          ·
            refine ⟨22673914377057159396647825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15115942918038106264431883 22673914377057159396647825)
            ·
              refine ⟨17005435782792869547485869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22673914377057159396647825 17005435782792869547485869)
              ·
                refine ⟨6377038418547326080307201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17005435782792869547485869 6377038418547326080307201)
                ·
                  refine ⟨4782778813910494560230401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6377038418547326080307201 4782778813910494560230401)
                  ·
                    refine ⟨3587084110432870920172801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4782778813910494560230401 3587084110432870920172801)
                    ·
                      refine ⟨2690313082824653190129601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3587084110432870920172801 2690313082824653190129601)
                      ·
                        rfl

theorem cell23_5239366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_5239366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239366 prefixEnd_5239366 := by exact prefixLift 5239366
  have htrace : WordTrace (prefixWord ++ tailWord_5239366) baseStart_5239366 baseEnd_5239366 := by
    simpa [prefixWord, tailWord_5239366, baseEnd_5239366] using wordTrace_append hprefix tailTrace_5239366
  have hstable : (prefixWord ++ tailWord_5239366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239366).length < 2 ^ (prefixWord ++ tailWord_5239366).sum := by decide
  have hdescent : baseEnd_5239366 < baseStart_5239366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239465 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 4, 3, 2]
def baseStart_5239465 : Nat := 118140960795 + 5239465 * 2 ^ 59
def prefixEnd_5239465 : Nat := 4983230072969 + 3 ^ 40 * 5239465 * 2
def baseEnd_5239465 : Nat := 2690363917409448302791645

theorem tailTrace_5239465 : CollatzResearch.WordTrace tailWord_5239465 prefixEnd_5239465 2690363917409448302791645 := by
  unfold tailWord_5239465
  simp only [CollatzResearch.WordTrace]
  refine ⟨191098987963320609226103849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127399325308880406150735899 191098987963320609226103849)
  ·
    refine ⟨143324240972490456919577887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191098987963320609226103849 143324240972490456919577887)
    ·
      refine ⟨214986361458735685379366831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143324240972490456919577887 214986361458735685379366831)
      ·
        refine ⟨322479542188103528069050247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214986361458735685379366831 322479542188103528069050247)
        ·
          refine ⟨483719313282155292103575371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322479542188103528069050247 483719313282155292103575371)
          ·
            refine ⟨725578969923232938155363057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483719313282155292103575371 725578969923232938155363057)
            ·
              refine ⟨544184227442424703616522293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725578969923232938155363057 544184227442424703616522293)
              ·
                refine ⟨51017271322727315964048965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 544184227442424703616522293 51017271322727315964048965)
                ·
                  refine ⟨9565738373011371743259181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51017271322727315964048965 9565738373011371743259181)
                  ·
                    refine ⟨3587151889879264403722193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9565738373011371743259181 3587151889879264403722193)
                    ·
                      refine ⟨2690363917409448302791645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3587151889879264403722193 2690363917409448302791645)
                      ·
                        rfl

theorem cell23_5239465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 3, 2].length) (baseStart_5239465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239465 prefixEnd_5239465 := by exact prefixLift 5239465
  have htrace : WordTrace (prefixWord ++ tailWord_5239465) baseStart_5239465 baseEnd_5239465 := by
    simpa [prefixWord, tailWord_5239465, baseEnd_5239465] using wordTrace_append hprefix tailTrace_5239465
  have hstable : (prefixWord ++ tailWord_5239465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239465).length < 2 ^ (prefixWord ++ tailWord_5239465).sum := by decide
  have hdescent : baseEnd_5239465 < baseStart_5239465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239466 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 3, 4]
def baseStart_5239466 : Nat := 118140960795 + 5239466 * 2 ^ 59
def prefixEnd_5239466 : Nat := 4983230072969 + 3 ^ 40 * 5239466 * 2
def baseEnd_5239466 : Nat := 896788143630034266293047

theorem tailTrace_5239466 : CollatzResearch.WordTrace tailWord_5239466 prefixEnd_5239466 896788143630034266293047 := by
  unfold tailWord_5239466
  simp only [CollatzResearch.WordTrace]
  refine ⟨47774756109079246599222563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127399349624211324264593501 47774756109079246599222563)
  ·
    refine ⟨71662134163618869898833845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47774756109079246599222563 71662134163618869898833845)
    ·
      refine ⟨6718325077839269053015673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71662134163618869898833845 6718325077839269053015673)
      ·
        refine ⟨5038743808379451789761755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6718325077839269053015673 5038743808379451789761755)
        ·
          refine ⟨7558115712569177684642633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5038743808379451789761755 7558115712569177684642633)
          ·
            refine ⟨5668586784426883263481975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7558115712569177684642633 5668586784426883263481975)
            ·
              refine ⟨8502880176640324895222963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5668586784426883263481975 8502880176640324895222963)
              ·
                refine ⟨12754320264960487342834445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8502880176640324895222963 12754320264960487342834445)
                ·
                  refine ⟨4782870099360182753562917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12754320264960487342834445 4782870099360182753562917)
                  ·
                    refine ⟨896788143630034266293047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4782870099360182753562917 896788143630034266293047)
                    ·
                      rfl

theorem cell23_5239466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_5239466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239466 prefixEnd_5239466 := by exact prefixLift 5239466
  have htrace : WordTrace (prefixWord ++ tailWord_5239466) baseStart_5239466 baseEnd_5239466 := by
    simpa [prefixWord, tailWord_5239466, baseEnd_5239466] using wordTrace_append hprefix tailTrace_5239466
  have hstable : (prefixWord ++ tailWord_5239466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239466).length < 2 ^ (prefixWord ++ tailWord_5239466).sum := by decide
  have hdescent : baseEnd_5239466 < baseStart_5239466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239479 : List Nat := [1, 1, 3, 1, 7, 1, 2, 1, 6]
def baseStart_5239479 : Nat := 118140960795 + 5239479 * 2 ^ 59
def prefixEnd_5239479 : Nat := 4983230072969 + 3 ^ 40 * 5239479 * 2
def baseEnd_5239479 : Nat := 298930122904290138668509

theorem tailTrace_5239479 : CollatzResearch.WordTrace tailWord_5239479 prefixEnd_5239479 298930122904290138668509 := by
  unfold tailWord_5239479
  simp only [CollatzResearch.WordTrace]
  refine ⟨191099498585269889617113491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127399665723513259744742327 191099498585269889617113491)
  ·
    refine ⟨286649247877904834425670237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191099498585269889617113491 286649247877904834425670237)
    ·
      refine ⟨107493467954214312909626339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286649247877904834425670237 107493467954214312909626339)
      ·
        refine ⟨161240201931321469364439509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107493467954214312909626339 161240201931321469364439509)
        ·
          refine ⟨3779067232765346938229051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 161240201931321469364439509 3779067232765346938229051)
          ·
            refine ⟨5668600849148020407343577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3779067232765346938229051 5668600849148020407343577)
            ·
              refine ⟨4251450636861015305507683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5668600849148020407343577 4251450636861015305507683)
              ·
                refine ⟨6377175955291522958261525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4251450636861015305507683 6377175955291522958261525)
                ·
                  refine ⟨298930122904290138668509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6377175955291522958261525 298930122904290138668509)
                  ·
                    rfl

theorem cell23_5239479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 6].length) (baseStart_5239479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239479 prefixEnd_5239479 := by exact prefixLift 5239479
  have htrace : WordTrace (prefixWord ++ tailWord_5239479) baseStart_5239479 baseEnd_5239479 := by
    simpa [prefixWord, tailWord_5239479, baseEnd_5239479] using wordTrace_append hprefix tailTrace_5239479
  have hstable : (prefixWord ++ tailWord_5239479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239479).length < 2 ^ (prefixWord ++ tailWord_5239479).sum := by decide
  have hdescent : baseEnd_5239479 < baseStart_5239479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239492 : List Nat := [2, 3, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_5239492 : Nat := 118140960795 + 5239492 * 2 ^ 59
def prefixEnd_5239492 : Nat := 4983230072969 + 3 ^ 40 * 5239492 * 2
def baseEnd_5239492 : Nat := 896792593795706565718007

theorem tailTrace_5239492 : CollatzResearch.WordTrace tailWord_5239492 prefixEnd_5239492 896792593795706565718007 := by
  unfold tailWord_5239492
  simp only [CollatzResearch.WordTrace]
  refine ⟨95549986367111396418668365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127399981822815195224891153 95549986367111396418668365)
  ·
    refine ⟨35831244887666773657000637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95549986367111396418668365 35831244887666773657000637)
    ·
      refine ⟨13436716832875040121375239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35831244887666773657000637 13436716832875040121375239)
      ·
        refine ⟨20155075249312560182062859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13436716832875040121375239 20155075249312560182062859)
        ·
          refine ⟨30232612873968840273094289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20155075249312560182062859 30232612873968840273094289)
          ·
            refine ⟨22674459655476630204820717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30232612873968840273094289 22674459655476630204820717)
            ·
              refine ⟨8502922370803736326807769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22674459655476630204820717 8502922370803736326807769)
              ·
                refine ⟨6377191778102802245105827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8502922370803736326807769 6377191778102802245105827)
                ·
                  refine ⟨9565787667154203367658741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6377191778102802245105827 9565787667154203367658741)
                  ·
                    refine ⟨896792593795706565718007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9565787667154203367658741 896792593795706565718007)
                    ·
                      rfl

theorem cell23_5239492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_5239492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239492 prefixEnd_5239492 := by exact prefixLift 5239492
  have htrace : WordTrace (prefixWord ++ tailWord_5239492) baseStart_5239492 baseEnd_5239492 := by
    simpa [prefixWord, tailWord_5239492, baseEnd_5239492] using wordTrace_append hprefix tailTrace_5239492
  have hstable : (prefixWord ++ tailWord_5239492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239492).length < 2 ^ (prefixWord ++ tailWord_5239492).sum := by decide
  have hdescent : baseEnd_5239492 < baseStart_5239492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239495 : List Nat := [1, 1, 4, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_5239495 : Nat := 118140960795 + 5239495 * 2 ^ 59
def prefixEnd_5239495 : Nat := 4983230072969 + 3 ^ 40 * 5239495 * 2
def baseEnd_5239495 : Nat := 2690379321829083185416507

theorem tailTrace_5239495 : CollatzResearch.WordTrace tailWord_5239495 prefixEnd_5239495 2690379321829083185416507 := by
  unfold tailWord_5239495
  simp only [CollatzResearch.WordTrace]
  refine ⟨191100082153211924349695939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127400054768807949566463959 191100082153211924349695939)
  ·
    refine ⟨286650123229817886524543909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191100082153211924349695939 286650123229817886524543909)
    ·
      refine ⟨53746898105590853723351983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286650123229817886524543909 53746898105590853723351983)
      ·
        refine ⟨80620347158386280585027975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53746898105590853723351983 80620347158386280585027975)
        ·
          refine ⟨120930520737579420877541963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80620347158386280585027975 120930520737579420877541963)
          ·
            refine ⟨181395781106369131316312945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120930520737579420877541963 181395781106369131316312945)
            ·
              refine ⟨136046835829776848487234709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181395781106369131316312945 136046835829776848487234709)
              ·
                refine ⟨6377195429520789772839127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136046835829776848487234709 6377195429520789772839127)
                ·
                  refine ⟨9565793144281184659258691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6377195429520789772839127 9565793144281184659258691)
                  ·
                    refine ⟨14348689716421776988888037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9565793144281184659258691 14348689716421776988888037)
                    ·
                      refine ⟨2690379321829083185416507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14348689716421776988888037 2690379321829083185416507)
                      ·
                        rfl

theorem cell23_5239495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_5239495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239495 prefixEnd_5239495 := by exact prefixLift 5239495
  have htrace : WordTrace (prefixWord ++ tailWord_5239495) baseStart_5239495 baseEnd_5239495 := by
    simpa [prefixWord, tailWord_5239495, baseEnd_5239495] using wordTrace_append hprefix tailTrace_5239495
  have hstable : (prefixWord ++ tailWord_5239495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239495).length < 2 ^ (prefixWord ++ tailWord_5239495).sum := by decide
  have hdescent : baseEnd_5239495 < baseStart_5239495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239523 : List Nat := [1, 1, 1, 7, 1, 3, 2, 2, 1, 1, 3]
def baseStart_5239523 : Nat := 118140960795 + 5239523 * 2 ^ 59
def prefixEnd_5239523 : Nat := 4983230072969 + 3 ^ 40 * 5239523 * 2
def baseEnd_5239523 : Nat := 2690393699287409075866379

theorem tailTrace_5239523 : CollatzResearch.WordTrace tailWord_5239523 prefixEnd_5239523 2690393699287409075866379 := by
  unfold tailWord_5239523
  simp only [CollatzResearch.WordTrace]
  refine ⟨191101103397110485131715223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127400735598073656754476815 191101103397110485131715223)
  ·
    refine ⟨286651655095665727697572835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191101103397110485131715223 286651655095665727697572835)
    ·
      refine ⟨429977482643498591546359253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286651655095665727697572835 429977482643498591546359253)
      ·
        refine ⟨10077597249456998239367795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 429977482643498591546359253 10077597249456998239367795)
        ·
          refine ⟨15116395874185497359051693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10077597249456998239367795 15116395874185497359051693)
          ·
            refine ⟨5668648452819561509644385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15116395874185497359051693 5668648452819561509644385)
            ·
              refine ⟨4251486339614671132233289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5668648452819561509644385 4251486339614671132233289)
              ·
                refine ⟨3188614754711003349174967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4251486339614671132233289 3188614754711003349174967)
                ·
                  refine ⟨4782922132066505023762451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3188614754711003349174967 4782922132066505023762451)
                  ·
                    refine ⟨7174383198099757535643677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4782922132066505023762451 7174383198099757535643677)
                    ·
                      refine ⟨2690393699287409075866379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7174383198099757535643677 2690393699287409075866379)
                      ·
                        rfl

theorem cell23_5239523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_5239523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239523 prefixEnd_5239523 := by exact prefixLift 5239523
  have htrace : WordTrace (prefixWord ++ tailWord_5239523) baseStart_5239523 baseEnd_5239523 := by
    simpa [prefixWord, tailWord_5239523, baseEnd_5239523] using wordTrace_append hprefix tailTrace_5239523
  have hstable : (prefixWord ++ tailWord_5239523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239523).length < 2 ^ (prefixWord ++ tailWord_5239523).sum := by decide
  have hdescent : baseEnd_5239523 < baseStart_5239523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239535 : List Nat := [1, 1, 2, 1, 5, 4, 1, 8]
def baseStart_5239535 : Nat := 118140960795 + 5239535 * 2 ^ 59
def prefixEnd_5239535 : Nat := 4983230072969 + 3 ^ 40 * 5239535 * 2
def baseEnd_5239535 : Nat := 99644439298343075145049

theorem tailTrace_5239535 : CollatzResearch.WordTrace tailWord_5239535 prefixEnd_5239535 99644439298343075145049 := by
  unfold tailWord_5239535
  simp only [CollatzResearch.WordTrace]
  refine ⟨191101541073067011181152059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127401027382044674120768039 191101541073067011181152059)
  ·
    refine ⟨286652311609600516771728089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191101541073067011181152059 286652311609600516771728089)
    ·
      refine ⟨214989233707200387578796067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286652311609600516771728089 214989233707200387578796067)
      ·
        refine ⟨322483850560800581368194101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214989233707200387578796067 322483850560800581368194101)
        ·
          refine ⟨30232860990075054503268197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 322483850560800581368194101 30232860990075054503268197)
          ·
            refine ⟨5668661435639072719362787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30232860990075054503268197 5668661435639072719362787)
            ·
              refine ⟨8502992153458609079044181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5668661435639072719362787 8502992153458609079044181)
              ·
                refine ⟨99644439298343075145049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8502992153458609079044181 99644439298343075145049)
                ·
                  rfl

theorem cell23_5239535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 8].length) (baseStart_5239535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239535 prefixEnd_5239535 := by exact prefixLift 5239535
  have htrace : WordTrace (prefixWord ++ tailWord_5239535) baseStart_5239535 baseEnd_5239535 := by
    simpa [prefixWord, tailWord_5239535, baseEnd_5239535] using wordTrace_append hprefix tailTrace_5239535
  have hstable : (prefixWord ++ tailWord_5239535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239535).length < 2 ^ (prefixWord ++ tailWord_5239535).sum := by decide
  have hdescent : baseEnd_5239535 < baseStart_5239535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239542 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_5239542 : Nat := 118140960795 + 5239542 * 2 ^ 59
def prefixEnd_5239542 : Nat := 4983230072969 + 3 ^ 40 * 5239542 * 2
def baseEnd_5239542 : Nat := 2690403455419844501528791

theorem tailTrace_5239542 : CollatzResearch.WordTrace tailWord_5239542 prefixEnd_5239542 2690403455419844501528791 := by
  unfold tailWord_5239542
  simp only [CollatzResearch.WordTrace]
  refine ⟨11943862274002603211041055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127401197589361100917771253 11943862274002603211041055)
  ·
    refine ⟨17915793411003904816561583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11943862274002603211041055 17915793411003904816561583)
    ·
      refine ⟨26873690116505857224842375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17915793411003904816561583 26873690116505857224842375)
      ·
        refine ⟨40310535174758785837263563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26873690116505857224842375 40310535174758785837263563)
        ·
          refine ⟨60465802762138178755895345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40310535174758785837263563 60465802762138178755895345)
          ·
            refine ⟨45349352071603634066921509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60465802762138178755895345 45349352071603634066921509)
            ·
              refine ⟨8503003513425681387547783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45349352071603634066921509 8503003513425681387547783)
              ·
                refine ⟨12754505270138522081321675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8503003513425681387547783 12754505270138522081321675)
                ·
                  refine ⟨19131757905207783121982513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12754505270138522081321675 19131757905207783121982513)
                  ·
                    refine ⟨14348818428905837341486885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19131757905207783121982513 14348818428905837341486885)
                    ·
                      refine ⟨2690403455419844501528791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14348818428905837341486885 2690403455419844501528791)
                      ·
                        rfl

theorem cell23_5239542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_5239542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239542 prefixEnd_5239542 := by exact prefixLift 5239542
  have htrace : WordTrace (prefixWord ++ tailWord_5239542) baseStart_5239542 baseEnd_5239542 := by
    simpa [prefixWord, tailWord_5239542, baseEnd_5239542] using wordTrace_append hprefix tailTrace_5239542
  have hstable : (prefixWord ++ tailWord_5239542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239542).length < 2 ^ (prefixWord ++ tailWord_5239542).sum := by decide
  have hdescent : baseEnd_5239542 < baseStart_5239542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239562 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_5239562 : Nat := 118140960795 + 5239562 * 2 ^ 59
def prefixEnd_5239562 : Nat := 4983230072969 + 3 ^ 40 * 5239562 * 2
def baseEnd_5239562 : Nat := 2690413725032934423278699

theorem tailTrace_5239562 : CollatzResearch.WordTrace tailWord_5239562 prefixEnd_5239562 2690413725032934423278699 := by
  unfold tailWord_5239562
  simp only [CollatzResearch.WordTrace]
  refine ⟨47775631460992298698096235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127401683895979463194923293 47775631460992298698096235)
  ·
    refine ⟨71663447191488448047144353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47775631460992298698096235 71663447191488448047144353)
    ·
      refine ⟨53747585393616336035358265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71663447191488448047144353 53747585393616336035358265)
      ·
        refine ⟨40310689045212252026518699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53747585393616336035358265 40310689045212252026518699)
        ·
          refine ⟨60466033567818378039778049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40310689045212252026518699 60466033567818378039778049)
          ·
            refine ⟨45349525175863783529833537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60466033567818378039778049 45349525175863783529833537)
            ·
              refine ⟨34012143881897837647375153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45349525175863783529833537 34012143881897837647375153)
              ·
                refine ⟨25509107911423378235531365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34012143881897837647375153 25509107911423378235531365)
                ·
                  refine ⟨4782957733391883419162131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25509107911423378235531365 4782957733391883419162131)
                  ·
                    refine ⟨7174436600087825128743197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4782957733391883419162131 7174436600087825128743197)
                    ·
                      refine ⟨2690413725032934423278699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7174436600087825128743197 2690413725032934423278699)
                      ·
                        rfl

theorem cell23_5239562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_5239562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239562 prefixEnd_5239562 := by exact prefixLift 5239562
  have htrace : WordTrace (prefixWord ++ tailWord_5239562) baseStart_5239562 baseEnd_5239562 := by
    simpa [prefixWord, tailWord_5239562, baseEnd_5239562] using wordTrace_append hprefix tailTrace_5239562
  have hstable : (prefixWord ++ tailWord_5239562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239562).length < 2 ^ (prefixWord ++ tailWord_5239562).sum := by decide
  have hdescent : baseEnd_5239562 < baseStart_5239562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239635 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 3]
def baseStart_5239635 : Nat := 118140960795 + 5239635 * 2 ^ 59
def prefixEnd_5239635 : Nat := 4983230072969 + 3 ^ 40 * 5239635 * 2
def baseEnd_5239635 : Nat := 2690451209120712637665863

theorem tailTrace_5239635 : CollatzResearch.WordTrace tailWord_5239635 prefixEnd_5239635 2690451209120712637665863 := by
  unfold tailWord_5239635
  simp only [CollatzResearch.WordTrace]
  refine ⟨191105188372704728259792359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127403458915136485506528239 191105188372704728259792359)
  ·
    refine ⟨286657782559057092389688539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191105188372704728259792359 286657782559057092389688539)
    ·
      refine ⟨429986673838585638584532809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286657782559057092389688539 429986673838585638584532809)
      ·
        refine ⟨322490005378939228938399607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429986673838585638584532809 322490005378939228938399607)
        ·
          refine ⟨483735008068408843407599411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322490005378939228938399607 483735008068408843407599411)
          ·
            refine ⟨725602512102613265111399117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483735008068408843407599411 725602512102613265111399117)
            ·
              refine ⟨272100942038479974416774669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 725602512102613265111399117 272100942038479974416774669)
              ·
                refine ⟨102037853264429990406290501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272100942038479974416774669 102037853264429990406290501)
                ·
                  refine ⟨19132097487080623201179469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102037853264429990406290501 19132097487080623201179469)
                  ·
                    refine ⟨7174536557655233700442301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19132097487080623201179469 7174536557655233700442301)
                    ·
                      refine ⟨2690451209120712637665863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7174536557655233700442301 2690451209120712637665863)
                      ·
                        rfl

theorem cell23_5239635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 3].length) (baseStart_5239635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239635 prefixEnd_5239635 := by exact prefixLift 5239635
  have htrace : WordTrace (prefixWord ++ tailWord_5239635) baseStart_5239635 baseEnd_5239635 := by
    simpa [prefixWord, tailWord_5239635, baseEnd_5239635] using wordTrace_append hprefix tailTrace_5239635
  have hstable : (prefixWord ++ tailWord_5239635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239635).length < 2 ^ (prefixWord ++ tailWord_5239635).sum := by decide
  have hdescent : baseEnd_5239635 < baseStart_5239635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239642 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 7]
def baseStart_5239642 : Nat := 118140960795 + 5239642 * 2 ^ 59
def prefixEnd_5239642 : Nat := 4983230072969 + 3 ^ 40 * 5239642 * 2
def baseEnd_5239642 : Nat := 298939422609477123364259

theorem tailTrace_5239642 : CollatzResearch.WordTrace tailWord_5239642 prefixEnd_5239642 298939422609477123364259 := by
  unfold tailWord_5239642
  simp only [CollatzResearch.WordTrace]
  refine ⟨47776360920919842113824295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127403629122452912303531453 47776360920919842113824295)
  ·
    refine ⟨71664541381379763170736443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47776360920919842113824295 71664541381379763170736443)
    ·
      refine ⟨107496812072069644756104665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71664541381379763170736443 107496812072069644756104665)
      ·
        refine ⟨80622609054052233567078499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107496812072069644756104665 80622609054052233567078499)
        ·
          refine ⟨120933913581078350350617749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80622609054052233567078499 120933913581078350350617749)
          ·
            refine ⟨5668777199113047672685207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120933913581078350350617749 5668777199113047672685207)
            ·
              refine ⟨8503165798669571509027811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5668777199113047672685207 8503165798669571509027811)
              ·
                refine ⟨12754748698004357263541717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8503165798669571509027811 12754748698004357263541717)
                ·
                  refine ⟨298939422609477123364259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12754748698004357263541717 298939422609477123364259)
                  ·
                    rfl

theorem cell23_5239642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_5239642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239642 prefixEnd_5239642 := by exact prefixLift 5239642
  have htrace : WordTrace (prefixWord ++ tailWord_5239642) baseStart_5239642 baseEnd_5239642 := by
    simpa [prefixWord, tailWord_5239642, baseEnd_5239642] using wordTrace_append hprefix tailTrace_5239642
  have hstable : (prefixWord ++ tailWord_5239642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239642).length < 2 ^ (prefixWord ++ tailWord_5239642).sum := by decide
  have hdescent : baseEnd_5239642 < baseStart_5239642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239675 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 4]
def baseStart_5239675 : Nat := 118140960795 + 5239675 * 2 ^ 59
def prefixEnd_5239675 : Nat := 4983230072969 + 3 ^ 40 * 5239675 * 2
def baseEnd_5239675 : Nat := 2690471748346892481165679

theorem tailTrace_5239675 : CollatzResearch.WordTrace tailWord_5239675 prefixEnd_5239675 2690471748346892481165679 := by
  unfold tailWord_5239675
  simp only [CollatzResearch.WordTrace]
  refine ⟨191106647292559815091248479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127404431528373210060832319 191106647292559815091248479)
  ·
    refine ⟨286659970938839722636872719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191106647292559815091248479 286659970938839722636872719)
    ·
      refine ⟨429989956408259583955309079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286659970938839722636872719 429989956408259583955309079)
      ·
        refine ⟨644984934612389375932963619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429989956408259583955309079 644984934612389375932963619)
        ·
          refine ⟨967477401918584063899445429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644984934612389375932963619 967477401918584063899445429)
          ·
            refine ⟨90701006429867255990573009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 967477401918584063899445429 90701006429867255990573009)
            ·
              refine ⟨68025754822400441992929757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90701006429867255990573009 68025754822400441992929757)
              ·
                refine ⟨25509658058400165747348659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68025754822400441992929757 25509658058400165747348659)
                ·
                  refine ⟨38264487087600248621022989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25509658058400165747348659 38264487087600248621022989)
                  ·
                    refine ⟨14349182657850093232883621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38264487087600248621022989 14349182657850093232883621)
                    ·
                      refine ⟨2690471748346892481165679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14349182657850093232883621 2690471748346892481165679)
                      ·
                        rfl

theorem cell23_5239675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 4].length) (baseStart_5239675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239675 prefixEnd_5239675 := by exact prefixLift 5239675
  have htrace : WordTrace (prefixWord ++ tailWord_5239675) baseStart_5239675 baseEnd_5239675 := by
    simpa [prefixWord, tailWord_5239675, baseEnd_5239675] using wordTrace_append hprefix tailTrace_5239675
  have hstable : (prefixWord ++ tailWord_5239675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239675).length < 2 ^ (prefixWord ++ tailWord_5239675).sum := by decide
  have hdescent : baseEnd_5239675 < baseStart_5239675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239692 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_5239692 : Nat := 118140960795 + 5239692 * 2 ^ 59
def prefixEnd_5239692 : Nat := 4983230072969 + 3 ^ 40 * 5239692 * 2
def baseEnd_5239692 : Nat := 2690480477518018914653101

theorem tailTrace_5239692 : CollatzResearch.WordTrace tailWord_5239692 prefixEnd_5239692 2690480477518018914653101 := by
  unfold tailWord_5239692
  simp only [CollatzResearch.WordTrace]
  refine ⟨95553633666749113497308665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127404844888998817996411553 95553633666749113497308665)
  ·
    refine ⟨71665225250061835122981499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95553633666749113497308665 71665225250061835122981499)
    ·
      refine ⟨107497837875092752684472249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71665225250061835122981499 107497837875092752684472249)
      ·
        refine ⟨80623378406319564513354187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107497837875092752684472249 80623378406319564513354187)
        ·
          refine ⟨120935067609479346770031281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80623378406319564513354187 120935067609479346770031281)
          ·
            refine ⟨90701300707109510077523461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120935067609479346770031281 90701300707109510077523461)
            ·
              refine ⟨17006493882583033139535649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90701300707109510077523461 17006493882583033139535649)
              ·
                refine ⟨12754870411937274854651737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17006493882583033139535649 12754870411937274854651737)
                ·
                  refine ⟨9566152808952956140988803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12754870411937274854651737 9566152808952956140988803)
                  ·
                    refine ⟨14349229213429434211483205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9566152808952956140988803 14349229213429434211483205)
                    ·
                      refine ⟨2690480477518018914653101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14349229213429434211483205 2690480477518018914653101)
                      ·
                        rfl

theorem cell23_5239692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_5239692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239692 prefixEnd_5239692 := by exact prefixLift 5239692
  have htrace : WordTrace (prefixWord ++ tailWord_5239692) baseStart_5239692 baseEnd_5239692 := by
    simpa [prefixWord, tailWord_5239692, baseEnd_5239692] using wordTrace_append hprefix tailTrace_5239692
  have hstable : (prefixWord ++ tailWord_5239692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239692).length < 2 ^ (prefixWord ++ tailWord_5239692).sum := by decide
  have hdescent : baseEnd_5239692 < baseStart_5239692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239705 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 2, 4, 4]
def baseStart_5239705 : Nat := 118140960795 + 5239705 * 2 ^ 59
def prefixEnd_5239705 : Nat := 4983230072969 + 3 ^ 40 * 5239705 * 2
def baseEnd_5239705 : Nat := 2690487152766527363790541

theorem tailTrace_5239705 : CollatzResearch.WordTrace tailWord_5239705 prefixEnd_5239705 2690487152766527363790541 := by
  unfold tailWord_5239705
  simp only [CollatzResearch.WordTrace]
  refine ⟨191107741482451130214840569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127405160988300753476560379 191107741482451130214840569)
  ·
    refine ⟨143330806111838347661130427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191107741482451130214840569 143330806111838347661130427)
    ·
      refine ⟨214996209167757521491695641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143330806111838347661130427 214996209167757521491695641)
      ·
        refine ⟨161247156875818141118771731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214996209167757521491695641 161247156875818141118771731)
        ·
          refine ⟨241870735313727211678157597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161247156875818141118771731 241870735313727211678157597)
          ·
            refine ⟨90701525742647704379309099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241870735313727211678157597 90701525742647704379309099)
            ·
              refine ⟨136052288613971556568963649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90701525742647704379309099 136052288613971556568963649)
              ·
                refine ⟨102039216460478667426722737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136052288613971556568963649 102039216460478667426722737)
                ·
                  refine ⟨76529412345359000570042053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102039216460478667426722737 76529412345359000570042053)
                  ·
                    refine ⟨14349264814754812606882885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76529412345359000570042053 14349264814754812606882885)
                    ·
                      refine ⟨2690487152766527363790541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14349264814754812606882885 2690487152766527363790541)
                      ·
                        rfl

theorem cell23_5239705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_5239705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239705 prefixEnd_5239705 := by exact prefixLift 5239705
  have htrace : WordTrace (prefixWord ++ tailWord_5239705) baseStart_5239705 baseEnd_5239705 := by
    simpa [prefixWord, tailWord_5239705, baseEnd_5239705] using wordTrace_append hprefix tailTrace_5239705
  have hstable : (prefixWord ++ tailWord_5239705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239705).length < 2 ^ (prefixWord ++ tailWord_5239705).sum := by decide
  have hdescent : baseEnd_5239705 < baseStart_5239705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239709 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_5239709 : Nat := 118140960795 + 5239709 * 2 ^ 59
def prefixEnd_5239709 : Nat := 4983230072969 + 3 ^ 40 * 5239709 * 2
def baseEnd_5239709 : Nat := 2690489206689145348140523

theorem tailTrace_5239709 : CollatzResearch.WordTrace tailWord_5239709 prefixEnd_5239709 2690489206689145348140523 := by
  unfold tailWord_5239709
  simp only [CollatzResearch.WordTrace]
  refine ⟨191107887374436638897986181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127405258249624425931990787 191107887374436638897986181)
  ·
    refine ⟨35832728882706869793372409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191107887374436638897986181 35832728882706869793372409)
    ·
      refine ⟨26874546662030152345029307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35832728882706869793372409 26874546662030152345029307)
      ·
        refine ⟨40311819993045228517543961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26874546662030152345029307 40311819993045228517543961)
        ·
          refine ⟨30233864994783921388157971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40311819993045228517543961 30233864994783921388157971)
          ·
            refine ⟨45350797492175882082236957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30233864994783921388157971 45350797492175882082236957)
            ·
              refine ⟨17006549059565955780838859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45350797492175882082236957 17006549059565955780838859)
              ·
                refine ⟨25509823589348933671258289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17006549059565955780838859 25509823589348933671258289)
                ·
                  refine ⟨19132367692011700253443717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25509823589348933671258289 19132367692011700253443717)
                  ·
                    refine ⟨3587318942252193797520697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19132367692011700253443717 3587318942252193797520697)
                    ·
                      refine ⟨2690489206689145348140523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3587318942252193797520697 2690489206689145348140523)
                      ·
                        rfl

theorem cell23_5239709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_5239709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239709 prefixEnd_5239709 := by exact prefixLift 5239709
  have htrace : WordTrace (prefixWord ++ tailWord_5239709) baseStart_5239709 baseEnd_5239709 := by
    simpa [prefixWord, tailWord_5239709, baseEnd_5239709] using wordTrace_append hprefix tailTrace_5239709
  have hstable : (prefixWord ++ tailWord_5239709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239709).length < 2 ^ (prefixWord ++ tailWord_5239709).sum := by decide
  have hdescent : baseEnd_5239709 < baseStart_5239709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239712 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 3]
def baseStart_5239712 : Nat := 118140960795 + 5239712 * 2 ^ 59
def prefixEnd_5239712 : Nat := 4983230072969 + 3 ^ 40 * 5239712 * 2
def baseEnd_5239712 : Nat := 2690490747131108836403009

theorem tailTrace_5239712 : CollatzResearch.WordTrace tailWord_5239712 prefixEnd_5239712 2690490747131108836403009 := by
  unfold tailWord_5239712
  simp only [CollatzResearch.WordTrace]
  refine ⟨95553998396712885205172695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127405331195617180273563593 95553998396712885205172695)
  ·
    refine ⟨143330997595069327807759043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95553998396712885205172695 143330997595069327807759043)
    ·
      refine ⟨214996496392603991711638565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143330997595069327807759043 214996496392603991711638565)
      ·
        refine ⟨40311843073613248445932231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214996496392603991711638565 40311843073613248445932231)
        ·
          refine ⟨60467764610419872668898347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40311843073613248445932231 60467764610419872668898347)
          ·
            refine ⟨90701646915629809003347521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60467764610419872668898347 90701646915629809003347521)
            ·
              refine ⟨68026235186722356752510641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90701646915629809003347521 68026235186722356752510641)
              ·
                refine ⟨51019676390041767564382981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68026235186722356752510641 51019676390041767564382981)
                ·
                  refine ⟨9566189323132831418321809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51019676390041767564382981 9566189323132831418321809)
                  ·
                    refine ⟨7174641992349623563741357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9566189323132831418321809 7174641992349623563741357)
                    ·
                      refine ⟨2690490747131108836403009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7174641992349623563741357 2690490747131108836403009)
                      ·
                        rfl

theorem cell23_5239712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_5239712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239712 prefixEnd_5239712 := by exact prefixLift 5239712
  have htrace : WordTrace (prefixWord ++ tailWord_5239712) baseStart_5239712 baseEnd_5239712 := by
    simpa [prefixWord, tailWord_5239712, baseEnd_5239712] using wordTrace_append hprefix tailTrace_5239712
  have hstable : (prefixWord ++ tailWord_5239712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239712).length < 2 ^ (prefixWord ++ tailWord_5239712).sum := by decide
  have hdescent : baseEnd_5239712 < baseStart_5239712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239729 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 1, 4, 3]
def baseStart_5239729 : Nat := 118140960795 + 5239729 * 2 ^ 59
def prefixEnd_5239729 : Nat := 4983230072969 + 3 ^ 40 * 5239729 * 2
def baseEnd_5239729 : Nat := 2690499476302235269890431

theorem tailTrace_5239729 : CollatzResearch.WordTrace tailWord_5239729 prefixEnd_5239729 2690499476302235269890431 := by
  unfold tailWord_5239729
  simp only [CollatzResearch.WordTrace]
  refine ⟨191108616834364182313714241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127405744556242788209142827 191108616834364182313714241)
  ·
    refine ⟨143331462625773136735285681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191108616834364182313714241 143331462625773136735285681)
    ·
      refine ⟨107498596969329852551464261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143331462625773136735285681 107498596969329852551464261)
      ·
        refine ⟨20155986931749347353399549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107498596969329852551464261 20155986931749347353399549)
        ·
          refine ⟨7558495099406005257524831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20155986931749347353399549 7558495099406005257524831)
          ·
            refine ⟨11337742649109007886287247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7558495099406005257524831 11337742649109007886287247)
            ·
              refine ⟨17006613973663511829430871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11337742649109007886287247 17006613973663511829430871)
              ·
                refine ⟨25509920960495267744146307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17006613973663511829430871 25509920960495267744146307)
                ·
                  refine ⟨38264881440742901616219461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25509920960495267744146307 38264881440742901616219461)
                  ·
                    refine ⟨7174665270139294053041149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38264881440742901616219461 7174665270139294053041149)
                    ·
                      refine ⟨2690499476302235269890431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7174665270139294053041149 2690499476302235269890431)
                      ·
                        rfl

theorem cell23_5239729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_5239729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239729 prefixEnd_5239729 := by exact prefixLift 5239729
  have htrace : WordTrace (prefixWord ++ tailWord_5239729) baseStart_5239729 baseEnd_5239729 := by
    simpa [prefixWord, tailWord_5239729, baseEnd_5239729] using wordTrace_append hprefix tailTrace_5239729
  have hstable : (prefixWord ++ tailWord_5239729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239729).length < 2 ^ (prefixWord ++ tailWord_5239729).sum := by decide
  have hdescent : baseEnd_5239729 < baseStart_5239729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239736 : List Nat := [2, 1, 2, 1, 2, 5, 2, 3, 1, 4]
def baseStart_5239736 : Nat := 118140960795 + 5239736 * 2 ^ 59
def prefixEnd_5239736 : Nat := 4983230072969 + 3 ^ 40 * 5239736 * 2
def baseEnd_5239736 : Nat := 896834356888938914167633

theorem tailTrace_5239736 : CollatzResearch.WordTrace tailWord_5239736 prefixEnd_5239736 896834356888938914167633 := by
  unfold tailWord_5239736
  simp only [CollatzResearch.WordTrace]
  refine ⟨95554436072669411254609531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127405914763559215006146041 95554436072669411254609531)
  ·
    refine ⟨143331654109004116881914297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95554436072669411254609531 143331654109004116881914297)
    ·
      refine ⟨107498740581753087661435723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143331654109004116881914297 107498740581753087661435723)
      ·
        refine ⟨161248110872629631492153585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107498740581753087661435723 161248110872629631492153585)
        ·
          refine ⟨120936083154472223619115189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161248110872629631492153585 120936083154472223619115189)
          ·
            refine ⟨11337757795731770964292049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120936083154472223619115189 11337757795731770964292049)
            ·
              refine ⟨8503318346798828223219037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11337757795731770964292049 8503318346798828223219037)
              ·
                refine ⟨3188744380049560583707139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8503318346798828223219037 3188744380049560583707139)
                ·
                  refine ⟨4783116570074340875560709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3188744380049560583707139 4783116570074340875560709)
                  ·
                    refine ⟨896834356888938914167633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4783116570074340875560709 896834356888938914167633)
                    ·
                      rfl

theorem cell23_5239736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_5239736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239736 prefixEnd_5239736 := by exact prefixLift 5239736
  have htrace : WordTrace (prefixWord ++ tailWord_5239736) baseStart_5239736 baseEnd_5239736 := by
    simpa [prefixWord, tailWord_5239736, baseEnd_5239736] using wordTrace_append hprefix tailTrace_5239736
  have hstable : (prefixWord ++ tailWord_5239736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239736).length < 2 ^ (prefixWord ++ tailWord_5239736).sum := by decide
  have hdescent : baseEnd_5239736 < baseStart_5239736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239759 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 3, 1, 3]
def baseStart_5239759 : Nat := 118140960795 + 5239759 * 2 ^ 59
def prefixEnd_5239759 : Nat := 4983230072969 + 3 ^ 40 * 5239759 * 2
def baseEnd_5239759 : Nat := 2690514880721870152515293

theorem tailTrace_5239759 : CollatzResearch.WordTrace tailWord_5239759 prefixEnd_5239759 2690514880721870152515293 := by
  unfold tailWord_5239759
  simp only [CollatzResearch.WordTrace]
  refine ⟨191109711024255497437306331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127406474016170331624870887 191109711024255497437306331)
  ·
    refine ⟨286664566536383246155959497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191109711024255497437306331 286664566536383246155959497)
    ·
      refine ⟨214998424902287434616969623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286664566536383246155959497 214998424902287434616969623)
      ·
        refine ⟨322497637353431151925454435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214998424902287434616969623 322497637353431151925454435)
        ·
          refine ⟨483746456030146727888181653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322497637353431151925454435 483746456030146727888181653)
          ·
            refine ⟨22675615126413127869758515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 483746456030146727888181653 22675615126413127869758515)
            ·
              refine ⟨34013422689619691804637773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22675615126413127869758515 34013422689619691804637773)
              ·
                refine ⟨12755033508607384426739165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34013422689619691804637773 12755033508607384426739165)
                ·
                  refine ⟨4783137565727769160027187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12755033508607384426739165 4783137565727769160027187)
                  ·
                    refine ⟨7174706348591653740040781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4783137565727769160027187 7174706348591653740040781)
                    ·
                      refine ⟨2690514880721870152515293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7174706348591653740040781 2690514880721870152515293)
                      ·
                        rfl

theorem cell23_5239759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 1, 3].length) (baseStart_5239759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239759 prefixEnd_5239759 := by exact prefixLift 5239759
  have htrace : WordTrace (prefixWord ++ tailWord_5239759) baseStart_5239759 baseEnd_5239759 := by
    simpa [prefixWord, tailWord_5239759, baseEnd_5239759] using wordTrace_append hprefix tailTrace_5239759
  have hstable : (prefixWord ++ tailWord_5239759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239759).length < 2 ^ (prefixWord ++ tailWord_5239759).sum := by decide
  have hdescent : baseEnd_5239759 < baseStart_5239759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239769 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 1, 5, 2]
def baseStart_5239769 : Nat := 118140960795 + 5239769 * 2 ^ 59
def prefixEnd_5239769 : Nat := 4983230072969 + 3 ^ 40 * 5239769 * 2
def baseEnd_5239769 : Nat := 2690520015528415113390247

theorem tailTrace_5239769 : CollatzResearch.WordTrace tailWord_5239769 prefixEnd_5239769 2690520015528415113390247 := by
  unfold tailWord_5239769
  simp only [CollatzResearch.WordTrace]
  refine ⟨191110075754219269145170361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127406717169479512763446907 191110075754219269145170361)
  ·
    refine ⟨143332556815664451858877771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191110075754219269145170361 143332556815664451858877771)
    ·
      refine ⟨214998835223496677788316657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143332556815664451858877771 214998835223496677788316657)
      ·
        refine ⟨161249126417622508341237493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214998835223496677788316657 161249126417622508341237493)
        ·
          refine ⟨15117105601652110156991015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161249126417622508341237493 15117105601652110156991015)
          ·
            refine ⟨22675658402478165235486523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15117105601652110156991015 22675658402478165235486523)
            ·
              refine ⟨34013487603717247853229785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22675658402478165235486523 34013487603717247853229785)
              ·
                refine ⟨25510115702787935889922339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34013487603717247853229785 25510115702787935889922339)
                ·
                  refine ⟨38265173554181903834883509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25510115702787935889922339 38265173554181903834883509)
                  ·
                    refine ⟨3587360020704553484520329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38265173554181903834883509 3587360020704553484520329)
                    ·
                      refine ⟨2690520015528415113390247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3587360020704553484520329 2690520015528415113390247)
                      ·
                        rfl

theorem cell23_5239769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 5, 2].length) (baseStart_5239769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239769 prefixEnd_5239769 := by exact prefixLift 5239769
  have htrace : WordTrace (prefixWord ++ tailWord_5239769) baseStart_5239769 baseEnd_5239769 := by
    simpa [prefixWord, tailWord_5239769, baseEnd_5239769] using wordTrace_append hprefix tailTrace_5239769
  have hstable : (prefixWord ++ tailWord_5239769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239769).length < 2 ^ (prefixWord ++ tailWord_5239769).sum := by decide
  have hdescent : baseEnd_5239769 < baseStart_5239769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239779 : List Nat := [1, 1, 1, 6, 1, 1, 4, 2, 1, 5]
def baseStart_5239779 : Nat := 118140960795 + 5239779 * 2 ^ 59
def prefixEnd_5239779 : Nat := 4983230072969 + 3 ^ 40 * 5239779 * 2
def baseEnd_5239779 : Nat := 896841716778320024755067

theorem tailTrace_5239779 : CollatzResearch.WordTrace tailWord_5239779 prefixEnd_5239779 896841716778320024755067 := by
  unfold tailWord_5239779
  simp only [CollatzResearch.WordTrace]
  refine ⟨191110440484183040853034391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127406960322788693902022927 191110440484183040853034391)
  ·
    refine ⟨286665660726274561279551587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191110440484183040853034391 286665660726274561279551587)
    ·
      refine ⟨429998491089411841919327381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286665660726274561279551587 429998491089411841919327381)
      ·
        refine ⟨20156179269816180089968471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 429998491089411841919327381 20156179269816180089968471)
        ·
          refine ⟨30234268904724270134952707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20156179269816180089968471 30234268904724270134952707)
          ·
            refine ⟨45351403357086405202429061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30234268904724270134952707 45351403357086405202429061)
            ·
              refine ⟨8503388129453700975455449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45351403357086405202429061 8503388129453700975455449)
              ·
                refine ⟨6377541097090275731591587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8503388129453700975455449 6377541097090275731591587)
                ·
                  refine ⟨9566311645635413597387381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6377541097090275731591587 9566311645635413597387381)
                  ·
                    refine ⟨896841716778320024755067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9566311645635413597387381 896841716778320024755067)
                    ·
                      rfl

theorem cell23_5239779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 5].length) (baseStart_5239779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239779 prefixEnd_5239779 := by exact prefixLift 5239779
  have htrace : WordTrace (prefixWord ++ tailWord_5239779) baseStart_5239779 baseEnd_5239779 := by
    simpa [prefixWord, tailWord_5239779, baseEnd_5239779] using wordTrace_append hprefix tailTrace_5239779
  have hstable : (prefixWord ++ tailWord_5239779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239779).length < 2 ^ (prefixWord ++ tailWord_5239779).sum := by decide
  have hdescent : baseEnd_5239779 < baseStart_5239779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239793 : List Nat := [1, 2, 2, 2, 4, 1, 3, 3, 1, 1, 3]
def baseStart_5239793 : Nat := 118140960795 + 5239793 * 2 ^ 59
def prefixEnd_5239793 : Nat := 4983230072969 + 3 ^ 40 * 5239793 * 2
def baseEnd_5239793 : Nat := 2690532339064123019490137

theorem tailTrace_5239793 : CollatzResearch.WordTrace tailWord_5239793 prefixEnd_5239793 2690532339064123019490137 := by
  unfold tailWord_5239793
  simp only [CollatzResearch.WordTrace]
  refine ⟨191110951106132321244044033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127407300737421547496029355 191110951106132321244044033)
  ·
    refine ⟨143333213329599240933033025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191110951106132321244044033 143333213329599240933033025)
    ·
      refine ⟨107499909997199430699774769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143333213329599240933033025 107499909997199430699774769)
      ·
        refine ⟨80624932497899573024831077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107499909997199430699774769 80624932497899573024831077)
        ·
          refine ⟨15117174843356169942155827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80624932497899573024831077 15117174843356169942155827)
          ·
            refine ⟨22675762265034254913233741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15117174843356169942155827 22675762265034254913233741)
            ·
              refine ⟨8503410849387845592462653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22675762265034254913233741 8503410849387845592462653)
              ·
                refine ⟨3188779068520442097173495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8503410849387845592462653 3188779068520442097173495)
                ·
                  refine ⟨4783168602780663145760243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3188779068520442097173495 4783168602780663145760243)
                  ·
                    refine ⟨7174752904170994718640365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4783168602780663145760243 7174752904170994718640365)
                    ·
                      refine ⟨2690532339064123019490137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7174752904170994718640365 2690532339064123019490137)
                      ·
                        rfl

theorem cell23_5239793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_5239793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239793 prefixEnd_5239793 := by exact prefixLift 5239793
  have htrace : WordTrace (prefixWord ++ tailWord_5239793) baseStart_5239793 baseEnd_5239793 := by
    simpa [prefixWord, tailWord_5239793, baseEnd_5239793] using wordTrace_append hprefix tailTrace_5239793
  have hstable : (prefixWord ++ tailWord_5239793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239793).length < 2 ^ (prefixWord ++ tailWord_5239793).sum := by decide
  have hdescent : baseEnd_5239793 < baseStart_5239793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239809 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 4, 4]
def baseStart_5239809 : Nat := 118140960795 + 5239809 * 2 ^ 59
def prefixEnd_5239809 : Nat := 4983230072969 + 3 ^ 40 * 5239809 * 2
def baseEnd_5239809 : Nat := 896846851584864985630021

theorem tailTrace_5239809 : CollatzResearch.WordTrace tailWord_5239809 prefixEnd_5239809 896846851584864985630021 := by
  unfold tailWord_5239809
  simp only [CollatzResearch.WordTrace]
  refine ⟨191111534674074355976626481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127407689782716237317750987 191111534674074355976626481)
  ·
    refine ⟨143333651005555766982469861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191111534674074355976626481 143333651005555766982469861)
    ·
      refine ⟨26875059563541706309213099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143333651005555766982469861 26875059563541706309213099)
      ·
        refine ⟨40312589345312559463819649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26875059563541706309213099 40312589345312559463819649)
        ·
          refine ⟨30234442008984419597864737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40312589345312559463819649 30234442008984419597864737)
          ·
            refine ⟨22675831506738314698398553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30234442008984419597864737 22675831506738314698398553)
            ·
              refine ⟨17006873630053736023798915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22675831506738314698398553 17006873630053736023798915)
              ·
                refine ⟨25510310445080604035698373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17006873630053736023798915 25510310445080604035698373)
                ·
                  refine ⟨4783183208452613256693445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25510310445080604035698373 4783183208452613256693445)
                  ·
                    refine ⟨896846851584864985630021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4783183208452613256693445 896846851584864985630021)
                    ·
                      rfl

theorem cell23_5239809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_5239809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239809 prefixEnd_5239809 := by exact prefixLift 5239809
  have htrace : WordTrace (prefixWord ++ tailWord_5239809) baseStart_5239809 baseEnd_5239809 := by
    simpa [prefixWord, tailWord_5239809, baseEnd_5239809] using wordTrace_append hprefix tailTrace_5239809
  have hstable : (prefixWord ++ tailWord_5239809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239809).length < 2 ^ (prefixWord ++ tailWord_5239809).sum := by decide
  have hdescent : baseEnd_5239809 < baseStart_5239809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239822 : List Nat := [4, 1, 1, 2, 2, 2, 1, 10]
def baseStart_5239822 : Nat := 118140960795 + 5239822 * 2 ^ 59
def prefixEnd_5239822 : Nat := 4983230072969 + 3 ^ 40 * 5239822 * 2
def baseEnd_5239822 : Nat := 99649897407522348371389

theorem tailTrace_5239822 : CollatzResearch.WordTrace tailWord_5239822 prefixEnd_5239822 99649897407522348371389 := by
  unfold tailWord_5239822
  simp only [CollatzResearch.WordTrace]
  refine ⟨23889001102878407399606215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127408005882018172797899813 23889001102878407399606215)
  ·
    refine ⟨35833501654317611099409323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23889001102878407399606215 35833501654317611099409323)
    ·
      refine ⟨53750252481476416649113985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35833501654317611099409323 53750252481476416649113985)
      ·
        refine ⟨40312689361107312486835489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53750252481476416649113985 40312689361107312486835489)
        ·
          refine ⟨30234517020830484365126617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40312689361107312486835489 30234517020830484365126617)
          ·
            refine ⟨22675887765622863273844963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30234517020830484365126617 22675887765622863273844963)
            ·
              refine ⟨34013831648434294910767445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22675887765622863273844963 34013831648434294910767445)
              ·
                refine ⟨99649897407522348371389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34013831648434294910767445 99649897407522348371389)
                ·
                  rfl

theorem cell23_5239822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_5239822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239822 prefixEnd_5239822 := by exact prefixLift 5239822
  have htrace : WordTrace (prefixWord ++ tailWord_5239822) baseStart_5239822 baseEnd_5239822 := by
    simpa [prefixWord, tailWord_5239822, baseEnd_5239822] using wordTrace_append hprefix tailTrace_5239822
  have hstable : (prefixWord ++ tailWord_5239822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239822).length < 2 ^ (prefixWord ++ tailWord_5239822).sum := by decide
  have hdescent : baseEnd_5239822 < baseStart_5239822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239836 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_5239836 : Nat := 118140960795 + 5239836 * 2 ^ 59
def prefixEnd_5239836 : Nat := 4983230072969 + 3 ^ 40 * 5239836 * 2
def baseEnd_5239836 : Nat := 2690554418732266351252439

theorem tailTrace_5239836 : CollatzResearch.WordTrace tailWord_5239836 prefixEnd_5239836 2690554418732266351252439 := by
  unfold tailWord_5239836
  simp only [CollatzResearch.WordTrace]
  refine ⟨95556259722488269793929681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127408346296651026391906241 95556259722488269793929681)
  ·
    refine ⟨71667194791866202345447261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95556259722488269793929681 71667194791866202345447261)
    ·
      refine ⟨26875198046949825879542723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71667194791866202345447261 26875198046949825879542723)
      ·
        refine ⟨40312797070424738819314085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26875198046949825879542723 40312797070424738819314085)
        ·
          refine ⟨7558649450704638528621391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40312797070424738819314085 7558649450704638528621391)
          ·
            refine ⟨11337974176056957792932087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7558649450704638528621391 11337974176056957792932087)
            ·
              refine ⟨17006961264085436689398131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11337974176056957792932087 17006961264085436689398131)
              ·
                refine ⟨25510441896128155034097197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17006961264085436689398131 25510441896128155034097197)
                ·
                  refine ⟨9566415711048058137786449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25510441896128155034097197 9566415711048058137786449)
                  ·
                    refine ⟨7174811783286043603339837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9566415711048058137786449 7174811783286043603339837)
                    ·
                      refine ⟨2690554418732266351252439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7174811783286043603339837 2690554418732266351252439)
                      ·
                        rfl

theorem cell23_5239836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_5239836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239836 prefixEnd_5239836 := by exact prefixLift 5239836
  have htrace : WordTrace (prefixWord ++ tailWord_5239836) baseStart_5239836 baseEnd_5239836 := by
    simpa [prefixWord, tailWord_5239836, baseEnd_5239836] using wordTrace_append hprefix tailTrace_5239836
  have hstable : (prefixWord ++ tailWord_5239836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239836).length < 2 ^ (prefixWord ++ tailWord_5239836).sum := by decide
  have hdescent : baseEnd_5239836 < baseStart_5239836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239866 : List Nat := [3, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3]
def baseStart_5239866 : Nat := 118140960795 + 5239866 * 2 ^ 59
def prefixEnd_5239866 : Nat := 4983230072969 + 3 ^ 40 * 5239866 * 2
def baseEnd_5239866 : Nat := 2690569823151901233877301

theorem tailTrace_5239866 : CollatzResearch.WordTrace tailWord_5239866 prefixEnd_5239866 2690569823151901233877301 := by
  unfold tailWord_5239866
  simp only [CollatzResearch.WordTrace]
  refine ⟨47778403408716963677862863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127409075756578569807634301 47778403408716963677862863)
  ·
    refine ⟨71667605113075445516794295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47778403408716963677862863 71667605113075445516794295)
    ·
      refine ⟨107501407669613168275191443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71667605113075445516794295 107501407669613168275191443)
      ·
        refine ⟨161252111504419752412787165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107501407669613168275191443 161252111504419752412787165)
        ·
          refine ⟨60469541814157407154795187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161252111504419752412787165 60469541814157407154795187)
          ·
            refine ⟨90704312721236110732192781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60469541814157407154795187 90704312721236110732192781)
            ·
              refine ⟨34014117270463541524572293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90704312721236110732192781 34014117270463541524572293)
              ·
                refine ⟨6377646988211914035857305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34014117270463541524572293 6377646988211914035857305)
                ·
                  refine ⟨4783235241158935526892979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6377646988211914035857305 4783235241158935526892979)
                  ·
                    refine ⟨7174852861738403290339469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4783235241158935526892979 7174852861738403290339469)
                    ·
                      refine ⟨2690569823151901233877301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7174852861738403290339469 2690569823151901233877301)
                      ·
                        rfl

theorem cell23_5239866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_5239866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239866 prefixEnd_5239866 := by exact prefixLift 5239866
  have htrace : WordTrace (prefixWord ++ tailWord_5239866) baseStart_5239866 baseEnd_5239866 := by
    simpa [prefixWord, tailWord_5239866, baseEnd_5239866] using wordTrace_append hprefix tailTrace_5239866
  have hstable : (prefixWord ++ tailWord_5239866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239866).length < 2 ^ (prefixWord ++ tailWord_5239866).sum := by decide
  have hdescent : baseEnd_5239866 < baseStart_5239866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239872 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 4]
def baseStart_5239872 : Nat := 118140960795 + 5239872 * 2 ^ 59
def prefixEnd_5239872 : Nat := 4983230072969 + 3 ^ 40 * 5239872 * 2
def baseEnd_5239872 : Nat := 2690572904035828210402273

theorem tailTrace_5239872 : CollatzResearch.WordTrace tailWord_5239872 prefixEnd_5239872 2690572904035828210402273 := by
  unfold tailWord_5239872
  simp only [CollatzResearch.WordTrace]
  refine ⟨95556916236423058868084935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127409221648564078490779913 95556916236423058868084935)
  ·
    refine ⟨143335374354634588302127403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95556916236423058868084935 143335374354634588302127403)
    ·
      refine ⟨215003061531951882453191105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143335374354634588302127403 215003061531951882453191105)
      ·
        refine ⟨161252296148963911839893329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215003061531951882453191105 161252296148963911839893329)
        ·
          refine ⟨120939222111722933879919997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161252296148963911839893329 120939222111722933879919997)
          ·
            refine ⟨45352208291896100204969999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120939222111722933879919997 45352208291896100204969999)
            ·
              refine ⟨68028312437844150307454999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45352208291896100204969999 68028312437844150307454999)
              ·
                refine ⟨102042468656766225461182499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68028312437844150307454999 102042468656766225461182499)
                ·
                  refine ⟨153063702985149338191773749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102042468656766225461182499 153063702985149338191773749)
                  ·
                    refine ⟨14349722154857750455478789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 153063702985149338191773749 14349722154857750455478789)
                    ·
                      refine ⟨2690572904035828210402273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14349722154857750455478789 2690572904035828210402273)
                      ·
                        rfl

theorem cell23_5239872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_5239872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239872 prefixEnd_5239872 := by exact prefixLift 5239872
  have htrace : WordTrace (prefixWord ++ tailWord_5239872) baseStart_5239872 baseEnd_5239872 := by
    simpa [prefixWord, tailWord_5239872, baseEnd_5239872] using wordTrace_append hprefix tailTrace_5239872
  have hstable : (prefixWord ++ tailWord_5239872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239872).length < 2 ^ (prefixWord ++ tailWord_5239872).sum := by decide
  have hdescent : baseEnd_5239872 < baseStart_5239872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239882 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 1, 8]
def baseStart_5239882 : Nat := 118140960795 + 5239882 * 2 ^ 59
def prefixEnd_5239882 : Nat := 4983230072969 + 3 ^ 40 * 5239882 * 2
def baseEnd_5239882 : Nat := 896859346280791057092409

theorem tailTrace_5239882 : CollatzResearch.WordTrace tailWord_5239882 prefixEnd_5239882 896859346280791057092409 := by
  unfold tailWord_5239882
  simp only [CollatzResearch.WordTrace]
  refine ⟨47778549300702472361008475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127409464801873259629355933 47778549300702472361008475)
  ·
    refine ⟨71667823951053708541512713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47778549300702472361008475 71667823951053708541512713)
    ·
      refine ⟨53750867963290281406134535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71667823951053708541512713 53750867963290281406134535)
      ·
        refine ⟨80626301944935422109201803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53750867963290281406134535 80626301944935422109201803)
        ·
          refine ⟨120939452917403133163802705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80626301944935422109201803 120939452917403133163802705)
          ·
            refine ⟨90704589688052349872852029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120939452917403133163802705 90704589688052349872852029)
            ·
              refine ⟨34014221133019631202319511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90704589688052349872852029 34014221133019631202319511)
              ·
                refine ⟨51021331699529446803479267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34014221133019631202319511 51021331699529446803479267)
                ·
                  refine ⟨76531997549294170205218901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51021331699529446803479267 76531997549294170205218901)
                  ·
                    refine ⟨896859346280791057092409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76531997549294170205218901 896859346280791057092409)
                    ·
                      rfl

theorem cell23_5239882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_5239882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239882 prefixEnd_5239882 := by exact prefixLift 5239882
  have htrace : WordTrace (prefixWord ++ tailWord_5239882) baseStart_5239882 baseEnd_5239882 := by
    simpa [prefixWord, tailWord_5239882, baseEnd_5239882] using wordTrace_append hprefix tailTrace_5239882
  have hstable : (prefixWord ++ tailWord_5239882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239882).length < 2 ^ (prefixWord ++ tailWord_5239882).sum := by decide
  have hdescent : baseEnd_5239882 < baseStart_5239882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239934 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5239934 : Nat := 118140960795 + 5239934 * 2 ^ 59
def prefixEnd_5239934 : Nat := 4983230072969 + 3 ^ 40 * 5239934 * 2
def baseEnd_5239934 : Nat := 2690604739836406967826989

theorem tailTrace_5239934 : CollatzResearch.WordTrace tailWord_5239934 prefixEnd_5239934 2690604739836406967826989 := by
  unfold tailWord_5239934
  simp only [CollatzResearch.WordTrace]
  refine ⟨23889511724827687790615857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127410729199081001549951237 23889511724827687790615857)
  ·
    refine ⟨17917133793620765842961893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23889511724827687790615857 17917133793620765842961893)
    ·
      refine ⟨3359462586303893595555355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17917133793620765842961893 3359462586303893595555355)
      ·
        refine ⟨5039193879455840393333033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3359462586303893595555355 5039193879455840393333033)
        ·
          refine ⟨3779395409591880294999775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5039193879455840393333033 3779395409591880294999775)
          ·
            refine ⟨5669093114387820442499663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3779395409591880294999775 5669093114387820442499663)
            ·
              refine ⟨8503639671581730663749495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5669093114387820442499663 8503639671581730663749495)
              ·
                refine ⟨12755459507372595995624243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8503639671581730663749495 12755459507372595995624243)
                ·
                  refine ⟨19133189261058893993436365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12755459507372595995624243 19133189261058893993436365)
                  ·
                    refine ⟨7174945972897085247538637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19133189261058893993436365 7174945972897085247538637)
                    ·
                      refine ⟨2690604739836406967826989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7174945972897085247538637 2690604739836406967826989)
                      ·
                        rfl

theorem cell23_5239934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5239934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239934 prefixEnd_5239934 := by exact prefixLift 5239934
  have htrace : WordTrace (prefixWord ++ tailWord_5239934) baseStart_5239934 baseEnd_5239934 := by
    simpa [prefixWord, tailWord_5239934, baseEnd_5239934] using wordTrace_append hprefix tailTrace_5239934
  have hstable : (prefixWord ++ tailWord_5239934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239934).length < 2 ^ (prefixWord ++ tailWord_5239934).sum := by decide
  have hdescent : baseEnd_5239934 < baseStart_5239934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239939 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 3]
def baseStart_5239939 : Nat := 118140960795 + 5239939 * 2 ^ 59
def prefixEnd_5239939 : Nat := 4983230072969 + 3 ^ 40 * 5239939 * 2
def baseEnd_5239939 : Nat := 2690607307239679448264465

theorem tailTrace_5239939 : CollatzResearch.WordTrace tailWord_5239939 prefixEnd_5239939 2690607307239679448264465 := by
  unfold tailWord_5239939
  simp only [CollatzResearch.WordTrace]
  refine ⟨191116276163603388178858871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127410850775735592119239247 191116276163603388178858871)
  ·
    refine ⟨286674414245405082268288307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191116276163603388178858871 286674414245405082268288307)
    ·
      refine ⟨430011621368107623402432461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286674414245405082268288307 430011621368107623402432461)
      ·
        refine ⟨161254358013040358775912173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430011621368107623402432461 161254358013040358775912173)
        ·
          refine ⟨60470384254890134540967065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161254358013040358775912173 60470384254890134540967065)
          ·
            refine ⟨45352788191167600905725299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60470384254890134540967065 45352788191167600905725299)
            ·
              refine ⟨68029182286751401358587949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45352788191167600905725299 68029182286751401358587949)
              ·
                refine ⟨25510943357531775509470481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68029182286751401358587949 25510943357531775509470481)
                ·
                  refine ⟨19133207518148831632102861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25510943357531775509470481 19133207518148831632102861)
                  ·
                    refine ⟨7174952819305811862038573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19133207518148831632102861 7174952819305811862038573)
                    ·
                      refine ⟨2690607307239679448264465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7174952819305811862038573 2690607307239679448264465)
                      ·
                        rfl

theorem cell23_5239939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_5239939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239939 prefixEnd_5239939 := by exact prefixLift 5239939
  have htrace : WordTrace (prefixWord ++ tailWord_5239939) baseStart_5239939 baseEnd_5239939 := by
    simpa [prefixWord, tailWord_5239939, baseEnd_5239939] using wordTrace_append hprefix tailTrace_5239939
  have hstable : (prefixWord ++ tailWord_5239939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239939).length < 2 ^ (prefixWord ++ tailWord_5239939).sum := by decide
  have hdescent : baseEnd_5239939 < baseStart_5239939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239952 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 7]
def baseStart_5239952 : Nat := 118140960795 + 5239952 * 2 ^ 59
def prefixEnd_5239952 : Nat := 4983230072969 + 3 ^ 40 * 5239952 * 2
def baseEnd_5239952 : Nat := 2690613982488187897401905

theorem tailTrace_5239952 : CollatzResearch.WordTrace tailWord_5239952 prefixEnd_5239952 2690613982488187897401905 := by
  unfold tailWord_5239952
  simp only [CollatzResearch.WordTrace]
  refine ⟨95558375156278145699541055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127411166875037527599388073 95558375156278145699541055)
  ·
    refine ⟨143337562734417218549311583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95558375156278145699541055 143337562734417218549311583)
    ·
      refine ⟨215006344101625827823967375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143337562734417218549311583 215006344101625827823967375)
      ·
        refine ⟨322509516152438741735951063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215006344101625827823967375 322509516152438741735951063)
        ·
          refine ⟨483764274228658112603926595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322509516152438741735951063 483764274228658112603926595)
          ·
            refine ⟨725646411342987168905889893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483764274228658112603926595 725646411342987168905889893)
            ·
              refine ⟨136058702126810094169854355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 725646411342987168905889893 136058702126810094169854355)
              ·
                refine ⟨204088053190215141254781533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136058702126810094169854355 204088053190215141254781533)
                ·
                  refine ⟨76533019946330677970543075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204088053190215141254781533 76533019946330677970543075)
                  ·
                    refine ⟨114799529919496016955814613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76533019946330677970543075 114799529919496016955814613)
                    ·
                      refine ⟨2690613982488187897401905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114799529919496016955814613 2690613982488187897401905)
                      ·
                        rfl

theorem cell23_5239952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_5239952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239952 prefixEnd_5239952 := by exact prefixLift 5239952
  have htrace : WordTrace (prefixWord ++ tailWord_5239952) baseStart_5239952 baseEnd_5239952 := by
    simpa [prefixWord, tailWord_5239952, baseEnd_5239952] using wordTrace_append hprefix tailTrace_5239952
  have hstable : (prefixWord ++ tailWord_5239952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239952).length < 2 ^ (prefixWord ++ tailWord_5239952).sum := by decide
  have hdescent : baseEnd_5239952 < baseStart_5239952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239959 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 1, 7]
def baseStart_5239959 : Nat := 118140960795 + 5239959 * 2 ^ 59
def prefixEnd_5239959 : Nat := 4983230072969 + 3 ^ 40 * 5239959 * 2
def baseEnd_5239959 : Nat := 896872525617589790004791

theorem tailTrace_5239959 : CollatzResearch.WordTrace tailWord_5239959 prefixEnd_5239959 896872525617589790004791 := by
  unfold tailWord_5239959
  simp only [CollatzResearch.WordTrace]
  refine ⟨191117005623530931594586931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127411337082353954396391287 191117005623530931594586931)
  ·
    refine ⟨286675508435296397391880397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191117005623530931594586931 286675508435296397391880397)
    ·
      refine ⟨107503315663236149021955149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286675508435296397391880397 107503315663236149021955149)
      ·
        refine ⟨40313743373713555883233181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107503315663236149021955149 40313743373713555883233181)
        ·
          refine ⟨15117653765142583456212443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40313743373713555883233181 15117653765142583456212443)
          ·
            refine ⟨22676480647713875184318665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15117653765142583456212443 22676480647713875184318665)
            ·
              refine ⟨17007360485785406388238999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22676480647713875184318665 17007360485785406388238999)
              ·
                refine ⟨25511040728678109582358499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17007360485785406388238999 25511040728678109582358499)
                ·
                  refine ⟨38266561093017164373537749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25511040728678109582358499 38266561093017164373537749)
                  ·
                    refine ⟨896872525617589790004791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38266561093017164373537749 896872525617589790004791)
                    ·
                      rfl

theorem cell23_5239959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_5239959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239959 prefixEnd_5239959 := by exact prefixLift 5239959
  have htrace : WordTrace (prefixWord ++ tailWord_5239959) baseStart_5239959 baseEnd_5239959 := by
    simpa [prefixWord, tailWord_5239959, baseEnd_5239959] using wordTrace_append hprefix tailTrace_5239959
  have hstable : (prefixWord ++ tailWord_5239959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239959).length < 2 ^ (prefixWord ++ tailWord_5239959).sum := by decide
  have hdescent : baseEnd_5239959 < baseStart_5239959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239969 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_5239969 : Nat := 118140960795 + 5239969 * 2 ^ 59
def prefixEnd_5239969 : Nat := 4983230072969 + 3 ^ 40 * 5239969 * 2
def baseEnd_5239969 : Nat := 2690622711659314330889327

theorem tailTrace_5239969 : CollatzResearch.WordTrace tailWord_5239969 prefixEnd_5239969 2690622711659314330889327 := by
  unfold tailWord_5239969
  simp only [CollatzResearch.WordTrace]
  refine ⟨191117370353494703302450961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127411580235663135534967307 191117370353494703302450961)
  ·
    refine ⟨143338027765121027476838221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191117370353494703302450961 143338027765121027476838221)
    ·
      refine ⟨53751760411920385303814333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143338027765121027476838221 53751760411920385303814333)
      ·
        refine ⟨20156910154470144488930375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53751760411920385303814333 20156910154470144488930375)
        ·
          refine ⟨30235365231705216733395563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20156910154470144488930375 30235365231705216733395563)
          ·
            refine ⟨45353047847557825100093345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30235365231705216733395563 45353047847557825100093345)
            ·
              refine ⟨34014785885668368825070009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45353047847557825100093345 34014785885668368825070009)
              ·
                refine ⟨25511089414251276618802507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34014785885668368825070009 25511089414251276618802507)
                ·
                  refine ⟨38266634121376914928203761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25511089414251276618802507 38266634121376914928203761)
                  ·
                    refine ⟨28699975591032686196152821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38266634121376914928203761 28699975591032686196152821)
                    ·
                      refine ⟨2690622711659314330889327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28699975591032686196152821 2690622711659314330889327)
                      ·
                        rfl

theorem cell23_5239969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_5239969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239969 prefixEnd_5239969 := by exact prefixLift 5239969
  have htrace : WordTrace (prefixWord ++ tailWord_5239969) baseStart_5239969 baseEnd_5239969 := by
    simpa [prefixWord, tailWord_5239969, baseEnd_5239969] using wordTrace_append hprefix tailTrace_5239969
  have hstable : (prefixWord ++ tailWord_5239969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239969).length < 2 ^ (prefixWord ++ tailWord_5239969).sum := by decide
  have hdescent : baseEnd_5239969 < baseStart_5239969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5239999 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 3]
def baseStart_5239999 : Nat := 118140960795 + 5239999 * 2 ^ 59
def prefixEnd_5239999 : Nat := 4983230072969 + 3 ^ 40 * 5239999 * 2
def baseEnd_5239999 : Nat := 2690638116078949213514189

theorem tailTrace_5239999 : CollatzResearch.WordTrace tailWord_5239999 prefixEnd_5239999 2690638116078949213514189 := by
  unfold tailWord_5239999
  simp only [CollatzResearch.WordTrace]
  refine ⟨191118464543386018426043051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127412309695590678950695367 191118464543386018426043051)
  ·
    refine ⟨286677696815079027639064577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191118464543386018426043051 286677696815079027639064577)
    ·
      refine ⟨215008272611309270729298433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286677696815079027639064577 215008272611309270729298433)
      ·
        refine ⟨161256204458481953046973825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215008272611309270729298433 161256204458481953046973825)
        ·
          refine ⟨120942153343861464785230369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161256204458481953046973825 120942153343861464785230369)
          ·
            refine ⟨90706615007896098588922777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120942153343861464785230369 90706615007896098588922777)
            ·
              refine ⟨68029961255922073941692083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90706615007896098588922777 68029961255922073941692083)
              ·
                refine ⟨102044941883883110912538125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68029961255922073941692083 102044941883883110912538125)
                ·
                  refine ⟨38266853206456166592201797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102044941883883110912538125 38266853206456166592201797)
                  ·
                    refine ⟨7175034976210531236037837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38266853206456166592201797 7175034976210531236037837)
                    ·
                      refine ⟨2690638116078949213514189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7175034976210531236037837 2690638116078949213514189)
                      ·
                        rfl

theorem cell23_5239999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_5239999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5239999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5239999 prefixEnd_5239999 := by exact prefixLift 5239999
  have htrace : WordTrace (prefixWord ++ tailWord_5239999) baseStart_5239999 baseEnd_5239999 := by
    simpa [prefixWord, tailWord_5239999, baseEnd_5239999] using wordTrace_append hprefix tailTrace_5239999
  have hstable : (prefixWord ++ tailWord_5239999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5239999).length < 2 ^ (prefixWord ++ tailWord_5239999).sum := by decide
  have hdescent : baseEnd_5239999 < baseStart_5239999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5239999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240063 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 3, 1, 3]
def baseStart_5240063 : Nat := 118140960795 + 5240063 * 2 ^ 59
def prefixEnd_5240063 : Nat := 4983230072969 + 3 ^ 40 * 5240063 * 2
def baseEnd_5240063 : Nat := 2690670978840836963113895

theorem tailTrace_5240063 : CollatzResearch.WordTrace tailWord_5240063 prefixEnd_5240063 2690670978840836963113895 := by
  unfold tailWord_5240063
  simp only [CollatzResearch.WordTrace]
  refine ⟨191120798815154157356372843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127413865876769438237581895 191120798815154157356372843)
  ·
    refine ⟨286681198222731236034559265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191120798815154157356372843 286681198222731236034559265)
    ·
      refine ⟨215010898667048427025919449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286681198222731236034559265 215010898667048427025919449)
      ·
        refine ⟨161258174000286320269439587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215010898667048427025919449 161258174000286320269439587)
        ·
          refine ⟨241887261000429480404159381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161258174000286320269439587 241887261000429480404159381)
          ·
            refine ⟨11338465359395131893944971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 241887261000429480404159381 11338465359395131893944971)
            ·
              refine ⟨17007698039092697840917457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11338465359395131893944971 17007698039092697840917457)
              ·
                refine ⟨12755773529319523380688093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17007698039092697840917457 12755773529319523380688093)
                ·
                  refine ⟨4783415073494821267758035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12755773529319523380688093 4783415073494821267758035)
                  ·
                    refine ⟨7175122610242231901637053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4783415073494821267758035 7175122610242231901637053)
                    ·
                      refine ⟨2690670978840836963113895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7175122610242231901637053 2690670978840836963113895)
                      ·
                        rfl

theorem cell23_5240063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_5240063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240063 prefixEnd_5240063 := by exact prefixLift 5240063
  have htrace : WordTrace (prefixWord ++ tailWord_5240063) baseStart_5240063 baseEnd_5240063 := by
    simpa [prefixWord, tailWord_5240063, baseEnd_5240063] using wordTrace_append hprefix tailTrace_5240063
  have hstable : (prefixWord ++ tailWord_5240063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240063).length < 2 ^ (prefixWord ++ tailWord_5240063).sum := by decide
  have hdescent : baseEnd_5240063 < baseStart_5240063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240089 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 5]
def baseStart_5240089 : Nat := 118140960795 + 5240089 * 2 ^ 59
def prefixEnd_5240089 : Nat := 4983230072969 + 3 ^ 40 * 5240089 * 2
def baseEnd_5240089 : Nat := 2690684329337853861388775

theorem tailTrace_5240089 : CollatzResearch.WordTrace tailWord_5240089 prefixEnd_5240089 2690684329337853861388775 := by
  unfold tailWord_5240089
  simp only [CollatzResearch.WordTrace]
  refine ⟨191121747113059963796819321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127414498075373309197879547 191121747113059963796819321)
  ·
    refine ⟨143341310334794972847614491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191121747113059963796819321 143341310334794972847614491)
    ·
      refine ⟨215011965502192459271421737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143341310334794972847614491 215011965502192459271421737)
      ·
        refine ⟨161258974126644344453566303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215011965502192459271421737 161258974126644344453566303)
        ·
          refine ⟨241888461189966516680349455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161258974126644344453566303 241888461189966516680349455)
          ·
            refine ⟨362832691784949775020524183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241888461189966516680349455 362832691784949775020524183)
            ·
              refine ⟨544249037677424662530786275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362832691784949775020524183 544249037677424662530786275)
              ·
                refine ⟨816373556516136993796179413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544249037677424662530786275 816373556516136993796179413)
                ·
                  refine ⟨19133755230846960792097955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 816373556516136993796179413 19133755230846960792097955)
                  ·
                    refine ⟨28700632846270441188146933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19133755230846960792097955 28700632846270441188146933)
                    ·
                      refine ⟨2690684329337853861388775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28700632846270441188146933 2690684329337853861388775)
                      ·
                        rfl

theorem cell23_5240089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_5240089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240089 prefixEnd_5240089 := by exact prefixLift 5240089
  have htrace : WordTrace (prefixWord ++ tailWord_5240089) baseStart_5240089 baseEnd_5240089 := by
    simpa [prefixWord, tailWord_5240089, baseEnd_5240089] using wordTrace_append hprefix tailTrace_5240089
  have hstable : (prefixWord ++ tailWord_5240089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240089).length < 2 ^ (prefixWord ++ tailWord_5240089).sum := by decide
  have hdescent : baseEnd_5240089 < baseStart_5240089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240113 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 1, 6]
def baseStart_5240113 : Nat := 118140960795 + 5240113 * 2 ^ 59
def prefixEnd_5240113 : Nat := 4983230072969 + 3 ^ 40 * 5240113 * 2
def baseEnd_5240113 : Nat := 896898884291187255829555

theorem tailTrace_5240113 : CollatzResearch.WordTrace tailWord_5240113 prefixEnd_5240113 896898884291187255829555 := by
  unfold tailWord_5240113
  simp only [CollatzResearch.WordTrace]
  refine ⟨191122622464973015895692993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127415081643315343930461995 191122622464973015895692993)
  ·
    refine ⟨143341966848729761921769745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191122622464973015895692993 143341966848729761921769745)
    ·
      refine ⟨107506475136547321441327309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143341966848729761921769745 107506475136547321441327309)
      ·
        refine ⟨40314928176205245540497741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107506475136547321441327309 40314928176205245540497741)
        ·
          refine ⟨15118098066076967077686653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40314928176205245540497741 15118098066076967077686653)
          ·
            refine ⟨5669286774778862654132495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15118098066076967077686653 5669286774778862654132495)
            ·
              refine ⟨8503930162168293981198743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5669286774778862654132495 8503930162168293981198743)
              ·
                refine ⟨12755895243252440971798115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8503930162168293981198743 12755895243252440971798115)
                ·
                  refine ⟨19133842864878661457697173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12755895243252440971798115 19133842864878661457697173)
                  ·
                    refine ⟨896898884291187255829555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19133842864878661457697173 896898884291187255829555)
                    ·
                      rfl

theorem cell23_5240113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_5240113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240113 prefixEnd_5240113 := by exact prefixLift 5240113
  have htrace : WordTrace (prefixWord ++ tailWord_5240113) baseStart_5240113 baseEnd_5240113 := by
    simpa [prefixWord, tailWord_5240113, baseEnd_5240113] using wordTrace_append hprefix tailTrace_5240113
  have hstable : (prefixWord ++ tailWord_5240113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240113).length < 2 ^ (prefixWord ++ tailWord_5240113).sum := by decide
  have hdescent : baseEnd_5240113 < baseStart_5240113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240126 : List Nat := [4, 2, 1, 2, 1, 1, 3, 9]
def baseStart_5240126 : Nat := 118140960795 + 5240126 * 2 ^ 59
def prefixEnd_5240126 : Nat := 4983230072969 + 3 ^ 40 * 5240126 * 2
def baseEnd_5240126 : Nat := 99655678819335933949115

theorem tailTrace_5240126 : CollatzResearch.WordTrace tailWord_5240126 prefixEnd_5240126 99655678819335933949115 := by
  unfold tailWord_5240126
  simp only [CollatzResearch.WordTrace]
  refine ⟨23890387076740739889489529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127415397742617279410610821 23890387076740739889489529)
  ·
    refine ⟨17917790307555554917117147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23890387076740739889489529 17917790307555554917117147)
    ·
      refine ⟨26876685461333332375675721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17917790307555554917117147 26876685461333332375675721)
      ·
        refine ⟨20157514095999999281756791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26876685461333332375675721 20157514095999999281756791)
        ·
          refine ⟨30236271143999998922635187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20157514095999999281756791 30236271143999998922635187)
          ·
            refine ⟨45354406715999998383952781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30236271143999998922635187 45354406715999998383952781)
            ·
              refine ⟨17007902518499999393982293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45354406715999998383952781 17007902518499999393982293)
              ·
                refine ⟨99655678819335933949115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17007902518499999393982293 99655678819335933949115)
                ·
                  rfl

theorem cell23_5240126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_5240126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240126 prefixEnd_5240126 := by exact prefixLift 5240126
  have htrace : WordTrace (prefixWord ++ tailWord_5240126) baseStart_5240126 baseEnd_5240126 := by
    simpa [prefixWord, tailWord_5240126, baseEnd_5240126] using wordTrace_append hprefix tailTrace_5240126
  have hstable : (prefixWord ++ tailWord_5240126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240126).length < 2 ^ (prefixWord ++ tailWord_5240126).sum := by decide
  have hdescent : baseEnd_5240126 < baseStart_5240126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240136 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_5240136 : Nat := 118140960795 + 5240136 * 2 ^ 59
def prefixEnd_5240136 : Nat := 4983230072969 + 3 ^ 40 * 5240136 * 2
def baseEnd_5240136 : Nat := 2690708462928615177501059

theorem tailTrace_5240136 : CollatzResearch.WordTrace tailWord_5240136 prefixEnd_5240136 2690708462928615177501059 := by
  unfold tailWord_5240136
  simp only [CollatzResearch.WordTrace]
  refine ⟨95561730671944845411890131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127415640895926460549186841 95561730671944845411890131)
  ·
    refine ⟨143342596007917268117835197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95561730671944845411890131 143342596007917268117835197)
    ·
      refine ⟨53753473502968975544188199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143342596007917268117835197 53753473502968975544188199)
      ·
        refine ⟨80630210254453463316282299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53753473502968975544188199 80630210254453463316282299)
        ·
          refine ⟨120945315381680194974423449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80630210254453463316282299 120945315381680194974423449)
          ·
            refine ⟨90708986536260146230817587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120945315381680194974423449 90708986536260146230817587)
            ·
              refine ⟨136063479804390219346226381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90708986536260146230817587 136063479804390219346226381)
              ·
                refine ⟨51023804926646332254834893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136063479804390219346226381 51023804926646332254834893)
                ·
                  refine ⟨19133926847492374595563085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51023804926646332254834893 19133926847492374595563085)
                  ·
                    refine ⟨7175222567809640473336157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19133926847492374595563085 7175222567809640473336157)
                    ·
                      refine ⟨2690708462928615177501059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7175222567809640473336157 2690708462928615177501059)
                      ·
                        rfl

theorem cell23_5240136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_5240136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240136 prefixEnd_5240136 := by exact prefixLift 5240136
  have htrace : WordTrace (prefixWord ++ tailWord_5240136) baseStart_5240136 baseEnd_5240136 := by
    simpa [prefixWord, tailWord_5240136, baseEnd_5240136] using wordTrace_append hprefix tailTrace_5240136
  have hstable : (prefixWord ++ tailWord_5240136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240136).length < 2 ^ (prefixWord ++ tailWord_5240136).sum := by decide
  have hdescent : baseEnd_5240136 < baseStart_5240136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240137 : List Nat := [1, 2, 1, 1, 2, 3, 5, 3, 1, 2, 2]
def baseStart_5240137 : Nat := 118140960795 + 5240137 * 2 ^ 59
def prefixEnd_5240137 : Nat := 4983230072969 + 3 ^ 40 * 5240137 * 2
def baseEnd_5240137 : Nat := 2690708976409269673588555

theorem tailTrace_5240137 : CollatzResearch.WordTrace tailWord_5240137 prefixEnd_5240137 2690708976409269673588555 := by
  unfold tailWord_5240137
  simp only [CollatzResearch.WordTrace]
  refine ⟨191123497816886067994566665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127415665211257378663044443 191123497816886067994566665)
  ·
    refine ⟨143342623362664550995924999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191123497816886067994566665 143342623362664550995924999)
    ·
      refine ⟨215013935043996826493887499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143342623362664550995924999 215013935043996826493887499)
      ·
        refine ⟨322520902565995239740831249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215013935043996826493887499 322520902565995239740831249)
        ·
          refine ⟨241890676924496429805623437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322520902565995239740831249 241890676924496429805623437)
          ·
            refine ⟨90709003846686161177108789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241890676924496429805623437 90709003846686161177108789)
            ·
              refine ⟨8503969110626827610353949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90709003846686161177108789 8503969110626827610353949)
              ·
                refine ⟨3188988416485060353882731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8503969110626827610353949 3188988416485060353882731)
                ·
                  refine ⟨4783482624727590530824097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3188988416485060353882731 4783482624727590530824097)
                  ·
                    refine ⟨3587611968545692898118073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4783482624727590530824097 3587611968545692898118073)
                    ·
                      refine ⟨2690708976409269673588555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3587611968545692898118073 2690708976409269673588555)
                      ·
                        rfl

theorem cell23_5240137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 1, 2, 2].length) (baseStart_5240137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240137 prefixEnd_5240137 := by exact prefixLift 5240137
  have htrace : WordTrace (prefixWord ++ tailWord_5240137) baseStart_5240137 baseEnd_5240137 := by
    simpa [prefixWord, tailWord_5240137, baseEnd_5240137] using wordTrace_append hprefix tailTrace_5240137
  have hstable : (prefixWord ++ tailWord_5240137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240137).length < 2 ^ (prefixWord ++ tailWord_5240137).sum := by decide
  have hdescent : baseEnd_5240137 < baseStart_5240137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240153 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 4, 1, 3]
def baseStart_5240153 : Nat := 118140960795 + 5240153 * 2 ^ 59
def prefixEnd_5240153 : Nat := 4983230072969 + 3 ^ 40 * 5240153 * 2
def baseEnd_5240153 : Nat := 2690717192099741610988481

theorem tailTrace_5240153 : CollatzResearch.WordTrace tailWord_5240153 prefixEnd_5240153 2690717192099741610988481 := by
  unfold tailWord_5240153
  simp only [CollatzResearch.WordTrace]
  refine ⟨191124081384828102727149113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127416054256552068484766075 191124081384828102727149113)
  ·
    refine ⟨143343061038621077045361835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191124081384828102727149113 143343061038621077045361835)
    ·
      refine ⟨215014591557931615568042753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143343061038621077045361835 215014591557931615568042753)
      ·
        refine ⟨161260943668448711676032065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215014591557931615568042753 161260943668448711676032065)
        ·
          refine ⟨120945707751336533757024049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161260943668448711676032065 120945707751336533757024049)
          ·
            refine ⟨90709280813502400317768037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120945707751336533757024049 90709280813502400317768037)
            ·
              refine ⟨17007990152531700059581507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90709280813502400317768037 17007990152531700059581507)
              ·
                refine ⟨25511985228797550089372261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17007990152531700059581507 25511985228797550089372261)
                ·
                  refine ⟨4783497230399540641757299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25511985228797550089372261 4783497230399540641757299)
                  ·
                    refine ⟨7175245845599310962635949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4783497230399540641757299 7175245845599310962635949)
                    ·
                      refine ⟨2690717192099741610988481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7175245845599310962635949 2690717192099741610988481)
                      ·
                        rfl

theorem cell23_5240153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_5240153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240153 prefixEnd_5240153 := by exact prefixLift 5240153
  have htrace : WordTrace (prefixWord ++ tailWord_5240153) baseStart_5240153 baseEnd_5240153 := by
    simpa [prefixWord, tailWord_5240153, baseEnd_5240153] using wordTrace_append hprefix tailTrace_5240153
  have hstable : (prefixWord ++ tailWord_5240153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240153).length < 2 ^ (prefixWord ++ tailWord_5240153).sum := by decide
  have hdescent : baseEnd_5240153 < baseStart_5240153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240174 : List Nat := [4, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_5240174 : Nat := 118140960795 + 5240174 * 2 ^ 59
def prefixEnd_5240174 : Nat := 4983230072969 + 3 ^ 40 * 5240174 * 2
def baseEnd_5240174 : Nat := 2690727975193486028825885

theorem tailTrace_5240174 : CollatzResearch.WordTrace tailWord_5240174 prefixEnd_5240174 2690727975193486028825885 := by
  unfold tailWord_5240174
  simp only [CollatzResearch.WordTrace]
  refine ⟨23890605914719002914207947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127416564878501348875775717 23890605914719002914207947)
  ·
    refine ⟨35835908872078504371311921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23890605914719002914207947 35835908872078504371311921)
    ·
      refine ⟨26876931654058878278483941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35835908872078504371311921 26876931654058878278483941)
      ·
        refine ⟨5039424685136039677215739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26876931654058878278483941 5039424685136039677215739)
        ·
          refine ⟨7559137027704059515823609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5039424685136039677215739 7559137027704059515823609)
          ·
            refine ⟨5669352770778044636867707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7559137027704059515823609 5669352770778044636867707)
            ·
              refine ⟨8504029156167066955301561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5669352770778044636867707 8504029156167066955301561)
              ·
                refine ⟨6378021867125300216476171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8504029156167066955301561 6378021867125300216476171)
                ·
                  refine ⟨9567032800687950324714257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6378021867125300216476171 9567032800687950324714257)
                  ·
                    refine ⟨7175274600515962743535693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9567032800687950324714257 7175274600515962743535693)
                    ·
                      refine ⟨2690727975193486028825885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7175274600515962743535693 2690727975193486028825885)
                      ·
                        rfl

theorem cell23_5240174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_5240174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240174 prefixEnd_5240174 := by exact prefixLift 5240174
  have htrace : WordTrace (prefixWord ++ tailWord_5240174) baseStart_5240174 baseEnd_5240174 := by
    simpa [prefixWord, tailWord_5240174, baseEnd_5240174] using wordTrace_append hprefix tailTrace_5240174
  have hstable : (prefixWord ++ tailWord_5240174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240174).length < 2 ^ (prefixWord ++ tailWord_5240174).sum := by decide
  have hdescent : baseEnd_5240174 < baseStart_5240174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240220 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 2, 6]
def baseStart_5240220 : Nat := 118140960795 + 5240220 * 2 ^ 59
def prefixEnd_5240220 : Nat := 4983230072969 + 3 ^ 40 * 5240220 * 2
def baseEnd_5240220 : Nat := 896917198434530949616891

theorem tailTrace_5240220 : CollatzResearch.WordTrace tailWord_5240220 prefixEnd_5240220 896917198434530949616891 := by
  unfold tailWord_5240220
  simp only [CollatzResearch.WordTrace]
  refine ⟨95563262537792686584919057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127417683383723582113225409 95563262537792686584919057)
  ·
    refine ⟨71672446903344514938689293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95563262537792686584919057 71672446903344514938689293)
    ·
      refine ⟨26877167588754193102008485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71672446903344514938689293 26877167588754193102008485)
      ·
        refine ⟨5039468922891411206626591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26877167588754193102008485 5039468922891411206626591)
        ·
          refine ⟨7559203384337116809939887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5039468922891411206626591 7559203384337116809939887)
          ·
            refine ⟨11338805076505675214909831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7559203384337116809939887 11338805076505675214909831)
            ·
              refine ⟨17008207614758512822364747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11338805076505675214909831 17008207614758512822364747)
              ·
                refine ⟨25512311422137769233547121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17008207614758512822364747 25512311422137769233547121)
                ·
                  refine ⟨19134233566603326925160341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25512311422137769233547121 19134233566603326925160341)
                  ·
                    refine ⟨896917198434530949616891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19134233566603326925160341 896917198434530949616891)
                    ·
                      rfl

theorem cell23_5240220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_5240220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240220 prefixEnd_5240220 := by exact prefixLift 5240220
  have htrace : WordTrace (prefixWord ++ tailWord_5240220) baseStart_5240220 baseEnd_5240220 := by
    simpa [prefixWord, tailWord_5240220, baseEnd_5240220] using wordTrace_append hprefix tailTrace_5240220
  have hstable : (prefixWord ++ tailWord_5240220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240220).length < 2 ^ (prefixWord ++ tailWord_5240220).sum := by decide
  have hdescent : baseEnd_5240220 < baseStart_5240220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240223 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 4]
def baseStart_5240223 : Nat := 118140960795 + 5240223 * 2 ^ 59
def prefixEnd_5240223 : Nat := 4983230072969 + 3 ^ 40 * 5240223 * 2
def baseEnd_5240223 : Nat := 2690753135745556337113159

theorem tailTrace_5240223 : CollatzResearch.WordTrace tailWord_5240223 prefixEnd_5240223 2690753135745556337113159 := by
  unfold tailWord_5240223
  simp only [CollatzResearch.WordTrace]
  refine ⟨191126634494574504682197323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127417756329716336454798215 191126634494574504682197323)
  ·
    refine ⟨286689951741861757023295985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191126634494574504682197323 286689951741861757023295985)
    ·
      refine ⟨215017463806396317767471989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286689951741861757023295985 215017463806396317767471989)
      ·
        refine ⟨20157887231849654790700499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215017463806396317767471989 20157887231849654790700499)
        ·
          refine ⟨30236830847774482186050749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20157887231849654790700499 30236830847774482186050749)
          ·
            refine ⟨11338811567915430819769031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30236830847774482186050749 11338811567915430819769031)
            ·
              refine ⟨17008217351873146229653547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11338811567915430819769031 17008217351873146229653547)
              ·
                refine ⟨25512326027809719344480321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17008217351873146229653547 25512326027809719344480321)
                ·
                  refine ⟨19134244520857289508360241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25512326027809719344480321 19134244520857289508360241)
                  ·
                    refine ⟨14350683390642967131270181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19134244520857289508360241 14350683390642967131270181)
                    ·
                      refine ⟨2690753135745556337113159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14350683390642967131270181 2690753135745556337113159)
                      ·
                        rfl

theorem cell23_5240223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_5240223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240223 prefixEnd_5240223 := by exact prefixLift 5240223
  have htrace : WordTrace (prefixWord ++ tailWord_5240223) baseStart_5240223 baseEnd_5240223 := by
    simpa [prefixWord, tailWord_5240223, baseEnd_5240223] using wordTrace_append hprefix tailTrace_5240223
  have hstable : (prefixWord ++ tailWord_5240223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240223).length < 2 ^ (prefixWord ++ tailWord_5240223).sum := by decide
  have hdescent : baseEnd_5240223 < baseStart_5240223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240256 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 5]
def baseStart_5240256 : Nat := 118140960795 + 5240256 * 2 ^ 59
def prefixEnd_5240256 : Nat := 4983230072969 + 3 ^ 40 * 5240256 * 2
def baseEnd_5240256 : Nat := 2690770080607154708000507

theorem tailTrace_5240256 : CollatzResearch.WordTrace tailWord_5240256 prefixEnd_5240256 2690770080607154708000507 := by
  unfold tailWord_5240256
  simp only [CollatzResearch.WordTrace]
  refine ⟨95563919051727475659074311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127418558735636634212099081 95563919051727475659074311)
  ·
    refine ⟨143345878577591213488611467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95563919051727475659074311 143345878577591213488611467)
    ·
      refine ⟨215018817866386820232917201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143345878577591213488611467 215018817866386820232917201)
      ·
        refine ⟨161264113399790115174687901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215018817866386820232917201 161264113399790115174687901)
        ·
          refine ⟨60474042524921293190507963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161264113399790115174687901 60474042524921293190507963)
          ·
            refine ⟨90711063787381939785761945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60474042524921293190507963 90711063787381939785761945)
            ·
              refine ⟨68033297840536454839321459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90711063787381939785761945 68033297840536454839321459)
              ·
                refine ⟨102049946760804682258982189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68033297840536454839321459 102049946760804682258982189)
                ·
                  refine ⟨38268730035301755847118321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102049946760804682258982189 38268730035301755847118321)
                  ·
                    refine ⟨28701547526476316885338741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38268730035301755847118321 28701547526476316885338741)
                    ·
                      refine ⟨2690770080607154708000507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28701547526476316885338741 2690770080607154708000507)
                      ·
                        rfl

theorem cell23_5240256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_5240256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240256 prefixEnd_5240256 := by exact prefixLift 5240256
  have htrace : WordTrace (prefixWord ++ tailWord_5240256) baseStart_5240256 baseEnd_5240256 := by
    simpa [prefixWord, tailWord_5240256, baseEnd_5240256] using wordTrace_append hprefix tailTrace_5240256
  have hstable : (prefixWord ++ tailWord_5240256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240256).length < 2 ^ (prefixWord ++ tailWord_5240256).sum := by decide
  have hdescent : baseEnd_5240256 < baseStart_5240256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240260 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_5240260 : Nat := 118140960795 + 5240260 * 2 ^ 59
def prefixEnd_5240260 : Nat := 4983230072969 + 3 ^ 40 * 5240260 * 2
def baseEnd_5240260 : Nat := 2690772134529772692350489

theorem tailTrace_5240260 : CollatzResearch.WordTrace tailWord_5240260 prefixEnd_5240260 2690772134529772692350489 := by
  unfold tailWord_5240260
  simp only [CollatzResearch.WordTrace]
  refine ⟨95563991997720230000647117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127418655996960306667529489 95563991997720230000647117)
  ·
    refine ⟨35836496999145086250242669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95563991997720230000647117 35836496999145086250242669)
    ·
      refine ⟨13438686374679407343841001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35836496999145086250242669 13438686374679407343841001)
      ·
        refine ⟨10079014781009555507880751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13438686374679407343841001 10079014781009555507880751)
        ·
          refine ⟨15118522171514333261821127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10079014781009555507880751 15118522171514333261821127)
          ·
            refine ⟨22677783257271499892731691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15118522171514333261821127 22677783257271499892731691)
            ·
              refine ⟨34016674885907249839097537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22677783257271499892731691 34016674885907249839097537)
              ·
                refine ⟨25512506164430437379323153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34016674885907249839097537 25512506164430437379323153)
                ·
                  refine ⟨19134379623322828034492365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25512506164430437379323153 19134379623322828034492365)
                  ·
                    refine ⟨7175392358746060512934637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19134379623322828034492365 7175392358746060512934637)
                    ·
                      refine ⟨2690772134529772692350489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7175392358746060512934637 2690772134529772692350489)
                      ·
                        rfl

theorem cell23_5240260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_5240260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240260 prefixEnd_5240260 := by exact prefixLift 5240260
  have htrace : WordTrace (prefixWord ++ tailWord_5240260) baseStart_5240260 baseEnd_5240260 := by
    simpa [prefixWord, tailWord_5240260, baseEnd_5240260] using wordTrace_append hprefix tailTrace_5240260
  have hstable : (prefixWord ++ tailWord_5240260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240260).length < 2 ^ (prefixWord ++ tailWord_5240260).sum := by decide
  have hdescent : baseEnd_5240260 < baseStart_5240260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240303 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 3]
def baseStart_5240303 : Nat := 118140960795 + 5240303 * 2 ^ 59
def prefixEnd_5240303 : Nat := 4983230072969 + 3 ^ 40 * 5240303 * 2
def baseEnd_5240303 : Nat := 2690794214197916024112791

theorem tailTrace_5240303 : CollatzResearch.WordTrace tailWord_5240303 prefixEnd_5240303 2690794214197916024112791 := by
  unfold tailWord_5240303
  simp only [CollatzResearch.WordTrace]
  refine ⟨191129552334284678345109563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127419701556189785563406375 191129552334284678345109563)
  ·
    refine ⟨286694328501427017517664345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191129552334284678345109563 286694328501427017517664345)
    ·
      refine ⟨215020746376070263138248259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286694328501427017517664345 215020746376070263138248259)
      ·
        refine ⟨322531119564105394707372389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215020746376070263138248259 322531119564105394707372389)
        ·
          refine ⟨60474584918269761507632323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 322531119564105394707372389 60474584918269761507632323)
          ·
            refine ⟨90711877377404642261448485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60474584918269761507632323 90711877377404642261448485)
            ·
              refine ⟨17008477008263370424021591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90711877377404642261448485 17008477008263370424021591)
              ·
                refine ⟨25512715512395055636032387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17008477008263370424021591 25512715512395055636032387)
                ·
                  refine ⟨38269073268592583454048581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25512715512395055636032387 38269073268592583454048581)
                  ·
                    refine ⟨7175451237861109397634109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38269073268592583454048581 7175451237861109397634109)
                    ·
                      refine ⟨2690794214197916024112791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7175451237861109397634109 2690794214197916024112791)
                      ·
                        rfl

theorem cell23_5240303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 3].length) (baseStart_5240303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240303 prefixEnd_5240303 := by exact prefixLift 5240303
  have htrace : WordTrace (prefixWord ++ tailWord_5240303) baseStart_5240303 baseEnd_5240303 := by
    simpa [prefixWord, tailWord_5240303, baseEnd_5240303] using wordTrace_append hprefix tailTrace_5240303
  have hstable : (prefixWord ++ tailWord_5240303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240303).length < 2 ^ (prefixWord ++ tailWord_5240303).sum := by decide
  have hdescent : baseEnd_5240303 < baseStart_5240303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240327 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 3, 4]
def baseStart_5240327 : Nat := 118140960795 + 5240327 * 2 ^ 59
def prefixEnd_5240327 : Nat := 4983230072969 + 3 ^ 40 * 5240327 * 2
def baseEnd_5240327 : Nat := 896935512577874643404227

theorem tailTrace_5240327 : CollatzResearch.WordTrace tailWord_5240327 prefixEnd_5240327 896935512577874643404227 := by
  unfold tailWord_5240327
  simp only [CollatzResearch.WordTrace]
  refine ⟨191130427686197730443983235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127420285124131820295988823 191130427686197730443983235)
  ·
    refine ⟨286695641529296595665974853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191130427686197730443983235 286695641529296595665974853)
    ·
      refine ⟨53755432786743111687370285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286695641529296595665974853 53755432786743111687370285)
      ·
        refine ⟨20158287295028666882763857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53755432786743111687370285 20158287295028666882763857)
        ·
          refine ⟨15118715471271500162072893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20158287295028666882763857 15118715471271500162072893)
          ·
            refine ⟨5669518301726812560777335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15118715471271500162072893 5669518301726812560777335)
            ·
              refine ⟨8504277452590218841166003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5669518301726812560777335 8504277452590218841166003)
              ·
                refine ⟨12756416178885328261749005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8504277452590218841166003 12756416178885328261749005)
                ·
                  refine ⟨4783656067081998098155877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12756416178885328261749005 4783656067081998098155877)
                  ·
                    refine ⟨896935512577874643404227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4783656067081998098155877 896935512577874643404227)
                    ·
                      rfl

theorem cell23_5240327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_5240327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240327 prefixEnd_5240327 := by exact prefixLift 5240327
  have htrace : WordTrace (prefixWord ++ tailWord_5240327) baseStart_5240327 baseEnd_5240327 := by
    simpa [prefixWord, tailWord_5240327, baseEnd_5240327] using wordTrace_append hprefix tailTrace_5240327
  have hstable : (prefixWord ++ tailWord_5240327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240327).length < 2 ^ (prefixWord ++ tailWord_5240327).sum := by decide
  have hdescent : baseEnd_5240327 < baseStart_5240327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240377 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 2, 3, 2]
def baseStart_5240377 : Nat := 118140960795 + 5240377 * 2 ^ 59
def prefixEnd_5240377 : Nat := 4983230072969 + 3 ^ 40 * 5240377 * 2
def baseEnd_5240377 : Nat := 2690832211766348734587451

theorem tailTrace_5240377 : CollatzResearch.WordTrace tailWord_5240377 prefixEnd_5240377 2690832211766348734587451 := by
  unfold tailWord_5240377
  simp only [CollatzResearch.WordTrace]
  refine ⟨191132251336016588983303385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127421500890677725988868923 191132251336016588983303385)
  ·
    refine ⟨143349188502012441737477539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191132251336016588983303385 143349188502012441737477539)
    ·
      refine ⟨215023782753018662606216309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143349188502012441737477539 215023782753018662606216309)
      ·
        refine ⟨20158479633095499619332779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215023782753018662606216309 20158479633095499619332779)
        ·
          refine ⟨30237719449643249428999169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20158479633095499619332779 30237719449643249428999169)
          ·
            refine ⟨22678289587232437071749377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30237719449643249428999169 22678289587232437071749377)
            ·
              refine ⟨17008717190424327803812033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22678289587232437071749377 17008717190424327803812033)
              ·
                refine ⟨12756537892818245852859025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17008717190424327803812033 12756537892818245852859025)
                ·
                  refine ⟨9567403419613684389644269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12756537892818245852859025 9567403419613684389644269)
                  ·
                    refine ⟨3587776282355131646116601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9567403419613684389644269 3587776282355131646116601)
                    ·
                      refine ⟨2690832211766348734587451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3587776282355131646116601 2690832211766348734587451)
                      ·
                        rfl

theorem cell23_5240377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_5240377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240377 prefixEnd_5240377 := by exact prefixLift 5240377
  have htrace : WordTrace (prefixWord ++ tailWord_5240377) baseStart_5240377 baseEnd_5240377 := by
    simpa [prefixWord, tailWord_5240377, baseEnd_5240377] using wordTrace_append hprefix tailTrace_5240377
  have hstable : (prefixWord ++ tailWord_5240377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240377).length < 2 ^ (prefixWord ++ tailWord_5240377).sum := by decide
  have hdescent : baseEnd_5240377 < baseStart_5240377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240393 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 5]
def baseStart_5240393 : Nat := 118140960795 + 5240393 * 2 ^ 59
def prefixEnd_5240393 : Nat := 4983230072969 + 3 ^ 40 * 5240393 * 2
def baseEnd_5240393 : Nat := 2690840427456820671987377

theorem tailTrace_5240393 : CollatzResearch.WordTrace tailWord_5240393 prefixEnd_5240393 2690840427456820671987377 := by
  unfold tailWord_5240393
  simp only [CollatzResearch.WordTrace]
  refine ⟨191132834903958623715885833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127421889935972415810590555 191132834903958623715885833)
  ·
    refine ⟨143349626177968967786914375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191132834903958623715885833 143349626177968967786914375)
    ·
      refine ⟨215024439266953451680371563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143349626177968967786914375 215024439266953451680371563)
      ·
        refine ⟨322536658900430177520557345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215024439266953451680371563 322536658900430177520557345)
        ·
          refine ⟨241902494175322633140418009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322536658900430177520557345 241902494175322633140418009)
          ·
            refine ⟨181426870631491974855313507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241902494175322633140418009 181426870631491974855313507)
            ·
              refine ⟨272140305947237962282970261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181426870631491974855313507 272140305947237962282970261)
              ·
                refine ⟨12756576841276779482014231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 272140305947237962282970261 12756576841276779482014231)
                ·
                  refine ⟨19134865261915169223021347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12756576841276779482014231 19134865261915169223021347)
                  ·
                    refine ⟨28702297892872753834532021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19134865261915169223021347 28702297892872753834532021)
                    ·
                      refine ⟨2690840427456820671987377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28702297892872753834532021 2690840427456820671987377)
                      ·
                        rfl

theorem cell23_5240393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_5240393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240393 prefixEnd_5240393 := by exact prefixLift 5240393
  have htrace : WordTrace (prefixWord ++ tailWord_5240393) baseStart_5240393 baseEnd_5240393 := by
    simpa [prefixWord, tailWord_5240393, baseEnd_5240393] using wordTrace_append hprefix tailTrace_5240393
  have hstable : (prefixWord ++ tailWord_5240393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240393).length < 2 ^ (prefixWord ++ tailWord_5240393).sum := by decide
  have hdescent : baseEnd_5240393 < baseStart_5240393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240400 : List Nat := [2, 1, 1, 1, 1, 3, 3, 5, 2, 4]
def baseStart_5240400 : Nat := 118140960795 + 5240400 * 2 ^ 59
def prefixEnd_5240400 : Nat := 4983230072969 + 3 ^ 40 * 5240400 * 2
def baseEnd_5240400 : Nat := 896948007273800714866615

theorem tailTrace_5240400 : CollatzResearch.WordTrace tailWord_5240400 prefixEnd_5240400 896948007273800714866615 := by
  unfold tailWord_5240400
  simp only [CollatzResearch.WordTrace]
  refine ⟨95566545107466631955695327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127422060143288842607593769 95566545107466631955695327)
  ·
    refine ⟨143349817661199947933542991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95566545107466631955695327 143349817661199947933542991)
    ·
      refine ⟨215024726491799921900314487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143349817661199947933542991 215024726491799921900314487)
      ·
        refine ⟨322537089737699882850471731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215024726491799921900314487 322537089737699882850471731)
        ·
          refine ⟨483805634606549824275707597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322537089737699882850471731 483805634606549824275707597)
          ·
            refine ⟨181427112977456184103390349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 483805634606549824275707597 181427112977456184103390349)
            ·
              refine ⟨68035167366546069038771381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181427112977456184103390349 68035167366546069038771381)
              ·
                refine ⟨6378296940613693972384817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68035167366546069038771381 6378296940613693972384817)
                ·
                  refine ⟨4783722705460270479288613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6378296940613693972384817 4783722705460270479288613)
                  ·
                    refine ⟨896948007273800714866615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4783722705460270479288613 896948007273800714866615)
                    ·
                      rfl

theorem cell23_5240400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 2, 4].length) (baseStart_5240400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240400 prefixEnd_5240400 := by exact prefixLift 5240400
  have htrace : WordTrace (prefixWord ++ tailWord_5240400) baseStart_5240400 baseEnd_5240400 := by
    simpa [prefixWord, tailWord_5240400, baseEnd_5240400] using wordTrace_append hprefix tailTrace_5240400
  have hstable : (prefixWord ++ tailWord_5240400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240400).length < 2 ^ (prefixWord ++ tailWord_5240400).sum := by decide
  have hdescent : baseEnd_5240400 < baseStart_5240400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240407 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 5, 2, 2]
def baseStart_5240407 : Nat := 118140960795 + 5240407 * 2 ^ 59
def prefixEnd_5240407 : Nat := 4983230072969 + 3 ^ 40 * 5240407 * 2
def baseEnd_5240407 : Nat := 2690847616185983617212313

theorem tailTrace_5240407 : CollatzResearch.WordTrace tailWord_5240407 prefixEnd_5240407 2690847616185983617212313 := by
  unfold tailWord_5240407
  simp only [CollatzResearch.WordTrace]
  refine ⟨191133345525907904106895475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127422230350605269404596983 191133345525907904106895475)
  ·
    refine ⟨286700018288861856160343213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191133345525907904106895475 286700018288861856160343213)
    ·
      refine ⟨107512506858323196060128705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286700018288861856160343213 107512506858323196060128705)
      ·
        refine ⟨80634380143742397045096529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107512506858323196060128705 80634380143742397045096529)
        ·
          refine ⟨60475785107806797783822397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80634380143742397045096529 60475785107806797783822397)
          ·
            refine ⟨22678419415427549168933399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60475785107806797783822397 22678419415427549168933399)
            ·
              refine ⟨34017629123141323753400099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22678419415427549168933399 34017629123141323753400099)
              ·
                refine ⟨51026443684711985630100149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34017629123141323753400099 51026443684711985630100149)
                ·
                  refine ⟨4783729095441748652821889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51026443684711985630100149 4783729095441748652821889)
                  ·
                    refine ⟨3587796821581311489616417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4783729095441748652821889 3587796821581311489616417)
                    ·
                      refine ⟨2690847616185983617212313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3587796821581311489616417 2690847616185983617212313)
                      ·
                        rfl

theorem cell23_5240407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_5240407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240407 prefixEnd_5240407 := by exact prefixLift 5240407
  have htrace : WordTrace (prefixWord ++ tailWord_5240407) baseStart_5240407 baseEnd_5240407 := by
    simpa [prefixWord, tailWord_5240407, baseEnd_5240407] using wordTrace_append hprefix tailTrace_5240407
  have hstable : (prefixWord ++ tailWord_5240407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240407).length < 2 ^ (prefixWord ++ tailWord_5240407).sum := by decide
  have hdescent : baseEnd_5240407 < baseStart_5240407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240420 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_5240420 : Nat := 118140960795 + 5240420 * 2 ^ 59
def prefixEnd_5240420 : Nat := 4983230072969 + 3 ^ 40 * 5240420 * 2
def baseEnd_5240420 : Nat := 2690854291434492066349753

theorem tailTrace_5240420 : CollatzResearch.WordTrace tailWord_5240420 prefixEnd_5240420 2690854291434492066349753 := by
  unfold tailWord_5240420
  simp only [CollatzResearch.WordTrace]
  refine ⟨95566909837430403663559357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127422546449907204884745809 95566909837430403663559357)
  ·
    refine ⟨35837591189036401373834759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95566909837430403663559357 35837591189036401373834759)
    ·
      refine ⟨53756386783554602060752139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35837591189036401373834759 53756386783554602060752139)
      ·
        refine ⟨80634580175331903091128209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53756386783554602060752139 80634580175331903091128209)
        ·
          refine ⟨60475935131498927318346157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80634580175331903091128209 60475935131498927318346157)
          ·
            refine ⟨22678475674312097744379809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60475935131498927318346157 22678475674312097744379809)
            ·
              refine ⟨17008856755734073308284857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22678475674312097744379809 17008856755734073308284857)
              ·
                refine ⟨12756642566800554981213643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17008856755734073308284857 12756642566800554981213643)
                ·
                  refine ⟨19134963850200832471820465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12756642566800554981213643 19134963850200832471820465)
                  ·
                    refine ⟨14351222887650624353865349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19134963850200832471820465 14351222887650624353865349)
                    ·
                      refine ⟨2690854291434492066349753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14351222887650624353865349 2690854291434492066349753)
                      ·
                        rfl

theorem cell23_5240420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_5240420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240420 prefixEnd_5240420 := by exact prefixLift 5240420
  have htrace : WordTrace (prefixWord ++ tailWord_5240420) baseStart_5240420 baseEnd_5240420 := by
    simpa [prefixWord, tailWord_5240420, baseEnd_5240420] using wordTrace_append hprefix tailTrace_5240420
  have hstable : (prefixWord ++ tailWord_5240420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240420).length < 2 ^ (prefixWord ++ tailWord_5240420).sum := by decide
  have hdescent : baseEnd_5240420 < baseStart_5240420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240424 : List Nat := [2, 1, 4, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_5240424 : Nat := 118140960795 + 5240424 * 2 ^ 59
def prefixEnd_5240424 : Nat := 4983230072969 + 3 ^ 40 * 5240424 * 2
def baseEnd_5240424 : Nat := 2690856345357110050699735

theorem tailTrace_5240424 : CollatzResearch.WordTrace tailWord_5240424 prefixEnd_5240424 2690856345357110050699735 := by
  unfold tailWord_5240424
  simp only [CollatzResearch.WordTrace]
  refine ⟨95566982783423158005132163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127422643711230877340176217 95566982783423158005132163)
  ·
    refine ⟨143350474175134737007698245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95566982783423158005132163 143350474175134737007698245)
    ·
      refine ⟨26878213907837763188943421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143350474175134737007698245 26878213907837763188943421)
      ·
        refine ⟨10079330215439161195853783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26878213907837763188943421 10079330215439161195853783)
        ·
          refine ⟨15118995323158741793780675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10079330215439161195853783 15118995323158741793780675)
          ·
            refine ⟨22678492984738112690671013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15118995323158741793780675 22678492984738112690671013)
            ·
              refine ⟨4252217434638396129500815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22678492984738112690671013 4252217434638396129500815)
              ·
                refine ⟨6378326151957594194251223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4252217434638396129500815 6378326151957594194251223)
                ·
                  refine ⟨9567489227936391291376835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6378326151957594194251223 9567489227936391291376835)
                  ·
                    refine ⟨14351233841904586937065253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9567489227936391291376835 14351233841904586937065253)
                    ·
                      refine ⟨2690856345357110050699735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14351233841904586937065253 2690856345357110050699735)
                      ·
                        rfl

theorem cell23_5240424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_5240424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240424 prefixEnd_5240424 := by exact prefixLift 5240424
  have htrace : WordTrace (prefixWord ++ tailWord_5240424) baseStart_5240424 baseEnd_5240424 := by
    simpa [prefixWord, tailWord_5240424, baseEnd_5240424] using wordTrace_append hprefix tailTrace_5240424
  have hstable : (prefixWord ++ tailWord_5240424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240424).length < 2 ^ (prefixWord ++ tailWord_5240424).sum := by decide
  have hdescent : baseEnd_5240424 < baseStart_5240424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240430 : List Nat := [4, 1, 2, 2, 3, 1, 10]
def baseStart_5240430 : Nat := 118140960795 + 5240430 * 2 ^ 59
def prefixEnd_5240430 : Nat := 4983230072969 + 3 ^ 40 * 5240430 * 2
def baseEnd_5240430 : Nat := 33220486743716506508947

theorem tailTrace_5240430 : CollatzResearch.WordTrace tailWord_5240430 prefixEnd_5240430 33220486743716506508947 := by
  unfold tailWord_5240430
  simp only [CollatzResearch.WordTrace]
  refine ⟨23891773050603072379372843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127422789603216386023321829 23891773050603072379372843)
  ·
    refine ⟨35837659575904608569059265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23891773050603072379372843 35837659575904608569059265)
    ·
      refine ⟨26878244681928456426794449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35837659575904608569059265 26878244681928456426794449)
      ·
        refine ⟨20158683511446342320095837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26878244681928456426794449 20158683511446342320095837)
        ·
          refine ⟨7559506316792378370035939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20158683511446342320095837 7559506316792378370035939)
          ·
            refine ⟨11339259475188567555053909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7559506316792378370035939 11339259475188567555053909)
            ·
              refine ⟨33220486743716506508947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11339259475188567555053909 33220486743716506508947)
              ·
                rfl

theorem cell23_5240430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 10].length) (baseStart_5240430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240430 prefixEnd_5240430 := by exact prefixLift 5240430
  have htrace : WordTrace (prefixWord ++ tailWord_5240430) baseStart_5240430 baseEnd_5240430 := by
    simpa [prefixWord, tailWord_5240430, baseEnd_5240430] using wordTrace_append hprefix tailTrace_5240430
  have hstable : (prefixWord ++ tailWord_5240430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240430).length < 2 ^ (prefixWord ++ tailWord_5240430).sum := by decide
  have hdescent : baseEnd_5240430 < baseStart_5240430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240434 : List Nat := [3, 2, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_5240434 : Nat := 118140960795 + 5240434 * 2 ^ 59
def prefixEnd_5240434 : Nat := 4983230072969 + 3 ^ 40 * 5240434 * 2
def baseEnd_5240434 : Nat := 896953826721218337191563

theorem tailTrace_5240434 : CollatzResearch.WordTrace tailWord_5240434 prefixEnd_5240434 896953826721218337191563 := by
  unfold tailWord_5240434
  simp only [CollatzResearch.WordTrace]
  refine ⟨47783582574202521929532089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127422886864540058478752237 47783582574202521929532089)
  ·
    refine ⟨35837686930651891447149067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47783582574202521929532089 35837686930651891447149067)
    ·
      refine ⟨53756530395977837170723601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35837686930651891447149067 53756530395977837170723601)
      ·
        refine ⟨40317397796983377878042701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53756530395977837170723601 40317397796983377878042701)
        ·
          refine ⟨15119024173868766704266013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40317397796983377878042701 15119024173868766704266013)
          ·
            refine ⟨5669634065200787514099755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15119024173868766704266013 5669634065200787514099755)
            ·
              refine ⟨8504451097801181271149633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5669634065200787514099755 8504451097801181271149633)
              ·
                refine ⟨6378338323350885953362225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8504451097801181271149633 6378338323350885953362225)
                ·
                  refine ⟨4783753742513164465021669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6378338323350885953362225 4783753742513164465021669)
                  ·
                    refine ⟨896953826721218337191563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4783753742513164465021669 896953826721218337191563)
                    ·
                      rfl

theorem cell23_5240434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_5240434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240434 prefixEnd_5240434 := by exact prefixLift 5240434
  have htrace : WordTrace (prefixWord ++ tailWord_5240434) baseStart_5240434 baseEnd_5240434 := by
    simpa [prefixWord, tailWord_5240434, baseEnd_5240434] using wordTrace_append hprefix tailTrace_5240434
  have hstable : (prefixWord ++ tailWord_5240434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240434).length < 2 ^ (prefixWord ++ tailWord_5240434).sum := by decide
  have hdescent : baseEnd_5240434 < baseStart_5240434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240457 : List Nat := [1, 2, 1, 1, 4, 1, 2, 5, 2, 1, 3]
def baseStart_5240457 : Nat := 118140960795 + 5240457 * 2 ^ 59
def prefixEnd_5240457 : Nat := 4983230072969 + 3 ^ 40 * 5240457 * 2
def baseEnd_5240457 : Nat := 2690873290218708421587083

theorem tailTrace_5240457 : CollatzResearch.WordTrace tailWord_5240457 prefixEnd_5240457 2690873290218708421587083 := by
  unfold tailWord_5240457
  simp only [CollatzResearch.WordTrace]
  refine ⟨191135169175726762646215625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127423446117151175097477083 191135169175726762646215625)
  ·
    refine ⟨143351376881795071984661719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191135169175726762646215625 143351376881795071984661719)
    ·
      refine ⟨215027065322692607976992579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143351376881795071984661719 215027065322692607976992579)
      ·
        refine ⟨322540597984038911965488869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215027065322692607976992579 322540597984038911965488869)
        ·
          refine ⟨60476362122007295993529163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 322540597984038911965488869 60476362122007295993529163)
          ·
            refine ⟨90714543183010943990293745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60476362122007295993529163 90714543183010943990293745)
            ·
              refine ⟨68035907387258207992720309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90714543183010943990293745 68035907387258207992720309)
              ·
                refine ⟨6378366317555456999317529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68035907387258207992720309 6378366317555456999317529)
                ·
                  refine ⟨4783774738166592749488147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6378366317555456999317529 4783774738166592749488147)
                  ·
                    refine ⟨7175662107249889124232221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4783774738166592749488147 7175662107249889124232221)
                    ·
                      refine ⟨2690873290218708421587083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7175662107249889124232221 2690873290218708421587083)
                      ·
                        rfl

theorem cell23_5240457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 1, 3].length) (baseStart_5240457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240457 prefixEnd_5240457 := by exact prefixLift 5240457
  have htrace : WordTrace (prefixWord ++ tailWord_5240457) baseStart_5240457 baseEnd_5240457 := by
    simpa [prefixWord, tailWord_5240457, baseEnd_5240457] using wordTrace_append hprefix tailTrace_5240457
  have hstable : (prefixWord ++ tailWord_5240457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240457).length < 2 ^ (prefixWord ++ tailWord_5240457).sum := by decide
  have hdescent : baseEnd_5240457 < baseStart_5240457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240473 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 4, 6]
def baseStart_5240473 : Nat := 118140960795 + 5240473 * 2 ^ 59
def prefixEnd_5240473 : Nat := 4983230072969 + 3 ^ 40 * 5240473 * 2
def baseEnd_5240473 : Nat := 896960501969726786329003

theorem tailTrace_5240473 : CollatzResearch.WordTrace tailWord_5240473 prefixEnd_5240473 896960501969726786329003 := by
  unfold tailWord_5240473
  simp only [CollatzResearch.WordTrace]
  refine ⟨191135752743668797378798073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127423835162445864919198715 191135752743668797378798073)
  ·
    refine ⟨143351814557751598034098555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191135752743668797378798073 143351814557751598034098555)
    ·
      refine ⟨215027721836627397051147833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143351814557751598034098555 215027721836627397051147833)
      ·
        refine ⟨161270791377470547788360875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215027721836627397051147833 161270791377470547788360875)
        ·
          refine ⟨241906187066205821682541313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161270791377470547788360875 241906187066205821682541313)
          ·
            refine ⟨181429640299654366261905985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241906187066205821682541313 181429640299654366261905985)
            ·
              refine ⟨136072230224740774696429489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181429640299654366261905985 136072230224740774696429489)
              ·
                refine ⟨102054172668555581022322117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136072230224740774696429489 102054172668555581022322117)
                ·
                  refine ⟨19135157375354171441685397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102054172668555581022322117 19135157375354171441685397)
                  ·
                    refine ⟨896960501969726786329003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19135157375354171441685397 896960501969726786329003)
                    ·
                      rfl

theorem cell23_5240473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_5240473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240473 prefixEnd_5240473 := by exact prefixLift 5240473
  have htrace : WordTrace (prefixWord ++ tailWord_5240473) baseStart_5240473 baseEnd_5240473 := by
    simpa [prefixWord, tailWord_5240473, baseEnd_5240473] using wordTrace_append hprefix tailTrace_5240473
  have hstable : (prefixWord ++ tailWord_5240473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240473).length < 2 ^ (prefixWord ++ tailWord_5240473).sum := by decide
  have hdescent : baseEnd_5240473 < baseStart_5240473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240484 : List Nat := [2, 3, 1, 2, 2, 2, 2, 3, 1, 3, 2]
def baseStart_5240484 : Nat := 118140960795 + 5240484 * 2 ^ 59
def prefixEnd_5240484 : Nat := 4983230072969 + 3 ^ 40 * 5240484 * 2
def baseEnd_5240484 : Nat := 2690887154196379815949459

theorem tailTrace_5240484 : CollatzResearch.WordTrace tailWord_5240484 prefixEnd_5240484 2690887154196379815949459 := by
  unfold tailWord_5240484
  simp only [CollatzResearch.WordTrace]
  refine ⟨95568076973314473128724253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127424102631085964171632337 95568076973314473128724253)
  ·
    refine ⟨35838028864992927423271595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95568076973314473128724253 35838028864992927423271595)
    ·
      refine ⟨53757043297489391134907393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35838028864992927423271595 53757043297489391134907393)
      ·
        refine ⟨40317782473117043351180545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53757043297489391134907393 40317782473117043351180545)
        ·
          refine ⟨30238336854837782513385409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40317782473117043351180545 30238336854837782513385409)
          ·
            refine ⟨22678752641128336885039057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30238336854837782513385409 22678752641128336885039057)
            ·
              refine ⟨17009064480846252663779293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22678752641128336885039057 17009064480846252663779293)
              ·
                refine ⟨6378399180317344748917235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17009064480846252663779293 6378399180317344748917235)
                ·
                  refine ⟨9567598770476017123375853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6378399180317344748917235 9567598770476017123375853)
                  ·
                    refine ⟨3587849538928506421265945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9567598770476017123375853 3587849538928506421265945)
                    ·
                      refine ⟨2690887154196379815949459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3587849538928506421265945 2690887154196379815949459)
                      ·
                        rfl

theorem cell23_5240484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_5240484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240484 prefixEnd_5240484 := by exact prefixLift 5240484
  have htrace : WordTrace (prefixWord ++ tailWord_5240484) baseStart_5240484 baseEnd_5240484 := by
    simpa [prefixWord, tailWord_5240484, baseEnd_5240484] using wordTrace_append hprefix tailTrace_5240484
  have hstable : (prefixWord ++ tailWord_5240484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240484).length < 2 ^ (prefixWord ++ tailWord_5240484).sum := by decide
  have hdescent : baseEnd_5240484 < baseStart_5240484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240518 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_5240518 : Nat := 118140960795 + 5240518 * 2 ^ 59
def prefixEnd_5240518 : Nat := 4983230072969 + 3 ^ 40 * 5240518 * 2
def baseEnd_5240518 : Nat := 2690904612538632682924303

theorem tailTrace_5240518 : CollatzResearch.WordTrace tailWord_5240518 prefixEnd_5240518 2690904612538632682924303 := by
  unfold tailWord_5240518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5973043563390805314505819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127424929352337180042790805 5973043563390805314505819)
  ·
    refine ⟨8959565345086207971758729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5973043563390805314505819 8959565345086207971758729)
    ·
      refine ⟨6719674008814655978819047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8959565345086207971758729 6719674008814655978819047)
      ·
        refine ⟨10079511013221983968228571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6719674008814655978819047 10079511013221983968228571)
        ·
          refine ⟨15119266519832975952342857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10079511013221983968228571 15119266519832975952342857)
          ·
            refine ⟨11339449889874731964257143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15119266519832975952342857 11339449889874731964257143)
            ·
              refine ⟨17009174834812097946385715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11339449889874731964257143 17009174834812097946385715)
              ·
                refine ⟨25513762252218146919578573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17009174834812097946385715 25513762252218146919578573)
                ·
                  refine ⟨9567660844581805094841965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25513762252218146919578573 9567660844581805094841965)
                  ·
                    refine ⟨3587872816718176910565737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9567660844581805094841965 3587872816718176910565737)
                    ·
                      refine ⟨2690904612538632682924303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3587872816718176910565737 2690904612538632682924303)
                      ·
                        rfl

theorem cell23_5240518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_5240518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240518 prefixEnd_5240518 := by exact prefixLift 5240518
  have htrace : WordTrace (prefixWord ++ tailWord_5240518) baseStart_5240518 baseEnd_5240518 := by
    simpa [prefixWord, tailWord_5240518, baseEnd_5240518] using wordTrace_append hprefix tailTrace_5240518
  have hstable : (prefixWord ++ tailWord_5240518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240518).length < 2 ^ (prefixWord ++ tailWord_5240518).sum := by decide
  have hdescent : baseEnd_5240518 < baseStart_5240518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240523 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 8]
def baseStart_5240523 : Nat := 118140960795 + 5240523 * 2 ^ 59
def prefixEnd_5240523 : Nat := 4983230072969 + 3 ^ 40 * 5240523 * 2
def baseEnd_5240523 : Nat := 2690907179941905163361779

theorem tailTrace_5240523 : CollatzResearch.WordTrace tailWord_5240523 prefixEnd_5240523 2690907179941905163361779 := by
  unfold tailWord_5240523
  simp only [CollatzResearch.WordTrace]
  refine ⟨191137576393487655918118223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127425050928991770612078815 191137576393487655918118223)
  ·
    refine ⟨286706364590231483877177335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191137576393487655918118223 286706364590231483877177335)
    ·
      refine ⟨430059546885347225815766003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286706364590231483877177335 430059546885347225815766003)
      ·
        refine ⟨645089320328020838723649005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430059546885347225815766003 645089320328020838723649005)
        ·
          refine ⟨241908495123007814521368377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 645089320328020838723649005 241908495123007814521368377)
          ·
            refine ⟨181431371342255860891026283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241908495123007814521368377 181431371342255860891026283)
            ·
              refine ⟨272147057013383791336539425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181431371342255860891026283 272147057013383791336539425)
              ·
                refine ⟨204110292760037843502404569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272147057013383791336539425 204110292760037843502404569)
                ·
                  refine ⟨153082719570028382626803427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204110292760037843502404569 153082719570028382626803427)
                  ·
                    refine ⟨229624079355042573940205141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 153082719570028382626803427 229624079355042573940205141)
                    ·
                      refine ⟨2690907179941905163361779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 229624079355042573940205141 2690907179941905163361779)
                      ·
                        rfl

theorem cell23_5240523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_5240523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240523 prefixEnd_5240523 := by exact prefixLift 5240523
  have htrace : WordTrace (prefixWord ++ tailWord_5240523) baseStart_5240523 baseEnd_5240523 := by
    simpa [prefixWord, tailWord_5240523, baseEnd_5240523] using wordTrace_append hprefix tailTrace_5240523
  have hstable : (prefixWord ++ tailWord_5240523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240523).length < 2 ^ (prefixWord ++ tailWord_5240523).sum := by decide
  have hdescent : baseEnd_5240523 < baseStart_5240523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240554 : List Nat := [3, 1, 3, 1, 1, 1, 6, 2, 5]
def baseStart_5240554 : Nat := 118140960795 + 5240554 * 2 ^ 59
def prefixEnd_5240554 : Nat := 4983230072969 + 3 ^ 40 * 5240554 * 2
def baseEnd_5240554 : Nat := 298991455315799393563793

theorem tailTrace_5240554 : CollatzResearch.WordTrace tailWord_5240554 prefixEnd_5240554 298991455315799393563793 := by
  unfold tailWord_5240554
  simp only [CollatzResearch.WordTrace]
  refine ⟨47784676764093837053124179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127425804704250232141664477 47784676764093837053124179)
  ·
    refine ⟨71677015146140755579686269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47784676764093837053124179 71677015146140755579686269)
    ·
      refine ⟨26878880679802783342382351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71677015146140755579686269 26878880679802783342382351)
      ·
        refine ⟨40318321019704175013573527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26878880679802783342382351 40318321019704175013573527)
        ·
          refine ⟨60477481529556262520360291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40318321019704175013573527 60477481529556262520360291)
          ·
            refine ⟨90716222294334393780540437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60477481529556262520360291 90716222294334393780540437)
            ·
              refine ⟨4252322920046924708462833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90716222294334393780540437 4252322920046924708462833)
              ·
                refine ⟨3189242190035193531347125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4252322920046924708462833 3189242190035193531347125)
                ·
                  refine ⟨298991455315799393563793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3189242190035193531347125 298991455315799393563793)
                  ·
                    rfl

theorem cell23_5240554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 5].length) (baseStart_5240554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240554 prefixEnd_5240554 := by exact prefixLift 5240554
  have htrace : WordTrace (prefixWord ++ tailWord_5240554) baseStart_5240554 baseEnd_5240554 := by
    simpa [prefixWord, tailWord_5240554, baseEnd_5240554] using wordTrace_append hprefix tailTrace_5240554
  have hstable : (prefixWord ++ tailWord_5240554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240554).length < 2 ^ (prefixWord ++ tailWord_5240554).sum := by decide
  have hdescent : baseEnd_5240554 < baseStart_5240554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240570 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_5240570 : Nat := 118140960795 + 5240570 * 2 ^ 59
def prefixEnd_5240570 : Nat := 4983230072969 + 3 ^ 40 * 5240570 * 2
def baseEnd_5240570 : Nat := 2690931313532666479474063

theorem tailTrace_5240570 : CollatzResearch.WordTrace tailWord_5240570 prefixEnd_5240570 2690931313532666479474063 := by
  unfold tailWord_5240570
  simp only [CollatzResearch.WordTrace]
  refine ⟨47784822656079345736269791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127426193749544921963386109 47784822656079345736269791)
  ·
    refine ⟨71677233984119018604404687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47784822656079345736269791 71677233984119018604404687)
    ·
      refine ⟨107515850976178527906607031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71677233984119018604404687 107515850976178527906607031)
      ·
        refine ⟨161273776464267791859910547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107515850976178527906607031 161273776464267791859910547)
        ·
          refine ⟨241910664696401687789865821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161273776464267791859910547 241910664696401687789865821)
          ·
            refine ⟨90716499261150632921199683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241910664696401687789865821 90716499261150632921199683)
            ·
              refine ⟨136074748891725949381799525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90716499261150632921199683 136074748891725949381799525)
              ·
                refine ⟨25514015417198615509087411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136074748891725949381799525 25514015417198615509087411)
                ·
                  refine ⟨38271023125797923263631117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25514015417198615509087411 38271023125797923263631117)
                  ·
                    refine ⟨14351633672174221223861669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38271023125797923263631117 14351633672174221223861669)
                    ·
                      refine ⟨2690931313532666479474063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14351633672174221223861669 2690931313532666479474063)
                      ·
                        rfl

theorem cell23_5240570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_5240570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240570 prefixEnd_5240570 := by exact prefixLift 5240570
  have htrace : WordTrace (prefixWord ++ tailWord_5240570) baseStart_5240570 baseEnd_5240570 := by
    simpa [prefixWord, tailWord_5240570, baseEnd_5240570] using wordTrace_append hprefix tailTrace_5240570
  have hstable : (prefixWord ++ tailWord_5240570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240570).length < 2 ^ (prefixWord ++ tailWord_5240570).sum := by decide
  have hdescent : baseEnd_5240570 < baseStart_5240570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240587 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 4]
def baseStart_5240587 : Nat := 118140960795 + 5240587 * 2 ^ 59
def prefixEnd_5240587 : Nat := 4983230072969 + 3 ^ 40 * 5240587 * 2
def baseEnd_5240587 : Nat := 2690940042703792912961485

theorem tailTrace_5240587 : CollatzResearch.WordTrace tailWord_5240587 prefixEnd_5240587 2690940042703792912961485 := by
  unfold tailWord_5240587
  simp only [CollatzResearch.WordTrace]
  refine ⟨191139910665255794848448015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127426607110170529898965343 191139910665255794848448015)
  ·
    refine ⟨286709865997883692272672023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191139910665255794848448015 286709865997883692272672023)
    ·
      refine ⟨430064798996825538409008035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286709865997883692272672023 430064798996825538409008035)
      ·
        refine ⟨645097198495238307613512053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430064798996825538409008035 645097198495238307613512053)
        ·
          refine ⟨60477862358928591338766755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 645097198495238307613512053 60477862358928591338766755)
          ·
            refine ⟨90716793538392887008150133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60477862358928591338766755 90716793538392887008150133)
            ·
              refine ⟨8504699394224333157014075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90716793538392887008150133 8504699394224333157014075)
              ·
                refine ⟨12757049091336499735521113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8504699394224333157014075 12757049091336499735521113)
                ·
                  refine ⟨9567786818502374801640835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12757049091336499735521113 9567786818502374801640835)
                  ·
                    refine ⟨14351680227753562202461253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9567786818502374801640835 14351680227753562202461253)
                    ·
                      refine ⟨2690940042703792912961485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14351680227753562202461253 2690940042703792912961485)
                      ·
                        rfl

theorem cell23_5240587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 4].length) (baseStart_5240587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240587 prefixEnd_5240587 := by exact prefixLift 5240587
  have htrace : WordTrace (prefixWord ++ tailWord_5240587) baseStart_5240587 baseEnd_5240587 := by
    simpa [prefixWord, tailWord_5240587, baseEnd_5240587] using wordTrace_append hprefix tailTrace_5240587
  have hstable : (prefixWord ++ tailWord_5240587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240587).length < 2 ^ (prefixWord ++ tailWord_5240587).sum := by decide
  have hdescent : baseEnd_5240587 < baseStart_5240587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240600 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_5240600 : Nat := 118140960795 + 5240600 * 2 ^ 59
def prefixEnd_5240600 : Nat := 4983230072969 + 3 ^ 40 * 5240600 * 2
def baseEnd_5240600 : Nat := 2690946717952301362098925

theorem tailTrace_5240600 : CollatzResearch.WordTrace tailWord_5240600 prefixEnd_5240600 2690946717952301362098925 := by
  unfold tailWord_5240600
  simp only [CollatzResearch.WordTrace]
  refine ⟨95570192407104349034335627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127426923209472465379114169 95570192407104349034335627)
  ·
    refine ⟨143355288610656523551503441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95570192407104349034335627 143355288610656523551503441)
    ·
      refine ⟨107516466457992392663627581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143355288610656523551503441 107516466457992392663627581)
      ·
        refine ⟨40318674921747147248860343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107516466457992392663627581 40318674921747147248860343)
        ·
          refine ⟨60478012382620720873290515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40318674921747147248860343 60478012382620720873290515)
          ·
            refine ⟨90717018573931081309935773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60478012382620720873290515 90717018573931081309935773)
            ·
              refine ⟨34018881965224155491225915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90717018573931081309935773 34018881965224155491225915)
              ·
                refine ⟨51028322947836233236838873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34018881965224155491225915 51028322947836233236838873)
                ·
                  refine ⟨38271242210877174927629155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51028322947836233236838873 38271242210877174927629155)
                  ·
                    refine ⟨57406863316315762391443733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38271242210877174927629155 57406863316315762391443733)
                    ·
                      refine ⟨2690946717952301362098925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57406863316315762391443733 2690946717952301362098925)
                      ·
                        rfl

theorem cell23_5240600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_5240600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240600 prefixEnd_5240600 := by exact prefixLift 5240600
  have htrace : WordTrace (prefixWord ++ tailWord_5240600) baseStart_5240600 baseEnd_5240600 := by
    simpa [prefixWord, tailWord_5240600, baseEnd_5240600] using wordTrace_append hprefix tailTrace_5240600
  have hstable : (prefixWord ++ tailWord_5240600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240600).length < 2 ^ (prefixWord ++ tailWord_5240600).sum := by decide
  have hdescent : baseEnd_5240600 < baseStart_5240600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240607 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 3]
def baseStart_5240607 : Nat := 118140960795 + 5240607 * 2 ^ 59
def prefixEnd_5240607 : Nat := 4983230072969 + 3 ^ 40 * 5240607 * 2
def baseEnd_5240607 : Nat := 2690950312316882834711393

theorem tailTrace_5240607 : CollatzResearch.WordTrace tailWord_5240607 prefixEnd_5240607 2690950312316882834711393 := by
  unfold tailWord_5240607
  simp only [CollatzResearch.WordTrace]
  refine ⟨191140640125183338264176075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127427093416788892176117383 191140640125183338264176075)
  ·
    refine ⟨286710960187775007396264113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191140640125183338264176075 286710960187775007396264113)
    ·
      refine ⟨215033220140831255547198085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286710960187775007396264113 215033220140831255547198085)
      ·
        refine ⟨40318728776405860415099641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215033220140831255547198085 40318728776405860415099641)
        ·
          refine ⟨30239046582304395311324731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40318728776405860415099641 30239046582304395311324731)
          ·
            refine ⟨45358569873456592966987097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30239046582304395311324731 45358569873456592966987097)
            ·
              refine ⟨34018927405092444725240323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45358569873456592966987097 34018927405092444725240323)
              ·
                refine ⟨51028391107638667087860485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34018927405092444725240323 51028391107638667087860485)
                ·
                  refine ⟨9567823332682250078973841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51028391107638667087860485 9567823332682250078973841)
                  ·
                    refine ⟨7175867499511687559230381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9567823332682250078973841 7175867499511687559230381)
                    ·
                      refine ⟨2690950312316882834711393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7175867499511687559230381 2690950312316882834711393)
                      ·
                        rfl

theorem cell23_5240607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_5240607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240607 prefixEnd_5240607 := by exact prefixLift 5240607
  have htrace : WordTrace (prefixWord ++ tailWord_5240607) baseStart_5240607 baseEnd_5240607 := by
    simpa [prefixWord, tailWord_5240607, baseEnd_5240607] using wordTrace_append hprefix tailTrace_5240607
  have hstable : (prefixWord ++ tailWord_5240607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240607).length < 2 ^ (prefixWord ++ tailWord_5240607).sum := by decide
  have hdescent : baseEnd_5240607 < baseStart_5240607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240671 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 3, 1, 3]
def baseStart_5240671 : Nat := 118140960795 + 5240671 * 2 ^ 59
def prefixEnd_5240671 : Nat := 4983230072969 + 3 ^ 40 * 5240671 * 2
def baseEnd_5240671 : Nat := 2690983175078770584311099

theorem tailTrace_5240671 : CollatzResearch.WordTrace tailWord_5240671 prefixEnd_5240671 2690983175078770584311099 := by
  unfold tailWord_5240671
  simp only [CollatzResearch.WordTrace]
  refine ⟨191142974396951477194505867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127428649597967651463003911 191142974396951477194505867)
  ·
    refine ⟨286714461595427215791758801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191142974396951477194505867 286714461595427215791758801)
    ·
      refine ⟨215035846196570411843819101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286714461595427215791758801 215035846196570411843819101)
      ·
        refine ⟨80638442323713904441432163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215035846196570411843819101 80638442323713904441432163)
        ·
          refine ⟨120957663485570856662148245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80638442323713904441432163 120957663485570856662148245)
          ·
            refine ⟨5669890475886133906038199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120957663485570856662148245 5669890475886133906038199)
            ·
              refine ⟨8504835713829200859057299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5669890475886133906038199 8504835713829200859057299)
              ·
                refine ⟨12757253570743801288585949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8504835713829200859057299 12757253570743801288585949)
                ·
                  refine ⟨4783970089028925483219731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12757253570743801288585949 4783970089028925483219731)
                  ·
                    refine ⟨7175955133543388224829597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4783970089028925483219731 7175955133543388224829597)
                    ·
                      refine ⟨2690983175078770584311099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7175955133543388224829597 2690983175078770584311099)
                      ·
                        rfl

theorem cell23_5240671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_5240671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240671 prefixEnd_5240671 := by exact prefixLift 5240671
  have htrace : WordTrace (prefixWord ++ tailWord_5240671) baseStart_5240671 baseEnd_5240671 := by
    simpa [prefixWord, tailWord_5240671, baseEnd_5240671] using wordTrace_append hprefix tailTrace_5240671
  have hstable : (prefixWord ++ tailWord_5240671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240671).length < 2 ^ (prefixWord ++ tailWord_5240671).sum := by decide
  have hdescent : baseEnd_5240671 < baseStart_5240671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240677 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_5240677 : Nat := 118140960795 + 5240677 * 2 ^ 59
def prefixEnd_5240677 : Nat := 4983230072969 + 3 ^ 40 * 5240677 * 2
def baseEnd_5240677 : Nat := 2690986255962697560836071

theorem tailTrace_5240677 : CollatzResearch.WordTrace tailWord_5240677 prefixEnd_5240677 2690986255962697560836071 := by
  unfold tailWord_5240677
  simp only [CollatzResearch.WordTrace]
  refine ⟨191143193234929740219224285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127428795489953160146149523 191143193234929740219224285)
  ·
    refine ⟨71678697463098652582209107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191143193234929740219224285 71678697463098652582209107)
    ·
      refine ⟨107518046194647978873313661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71678697463098652582209107 107518046194647978873313661)
      ·
        refine ⟨40319267322992992077492623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107518046194647978873313661 40319267322992992077492623)
        ·
          refine ⟨60478900984489488116238935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40319267322992992077492623 60478900984489488116238935)
          ·
            refine ⟨90718351476734232174358403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60478900984489488116238935 90718351476734232174358403)
            ·
              refine ⟨136077527215101348261537605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90718351476734232174358403 136077527215101348261537605)
              ·
                refine ⟨25514536352831502799038301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136077527215101348261537605 25514536352831502799038301)
                ·
                  refine ⟨9567951132311813549639363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25514536352831502799038301 9567951132311813549639363)
                  ·
                    refine ⟨14351926698467720324459045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9567951132311813549639363 14351926698467720324459045)
                    ·
                      refine ⟨2690986255962697560836071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14351926698467720324459045 2690986255962697560836071)
                      ·
                        rfl

theorem cell23_5240677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_5240677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240677 prefixEnd_5240677 := by exact prefixLift 5240677
  have htrace : WordTrace (prefixWord ++ tailWord_5240677) baseStart_5240677 baseEnd_5240677 := by
    simpa [prefixWord, tailWord_5240677, baseEnd_5240677] using wordTrace_append hprefix tailTrace_5240677
  have hstable : (prefixWord ++ tailWord_5240677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240677).length < 2 ^ (prefixWord ++ tailWord_5240677).sum := by decide
  have hdescent : baseEnd_5240677 < baseStart_5240677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240707 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 4]
def baseStart_5240707 : Nat := 118140960795 + 5240707 * 2 ^ 59
def prefixEnd_5240707 : Nat := 4983230072969 + 3 ^ 40 * 5240707 * 2
def baseEnd_5240707 : Nat := 2691001660382332443460933

theorem tailTrace_5240707 : CollatzResearch.WordTrace tailWord_5240707 prefixEnd_5240707 2691001660382332443460933 := by
  unfold tailWord_5240707
  simp only [CollatzResearch.WordTrace]
  refine ⟨191144287424821055342816375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127429524949880703561877583 191144287424821055342816375)
  ·
    refine ⟨286716431137231583014224563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191144287424821055342816375 286716431137231583014224563)
    ·
      refine ⟨430074646705847374521336845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286716431137231583014224563 430074646705847374521336845)
      ·
        refine ⟨161277992514692765445501317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430074646705847374521336845 161277992514692765445501317)
        ·
          refine ⟨30239623596504893521031497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161277992514692765445501317 30239623596504893521031497)
          ·
            refine ⟨22679717697378670140773623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30239623596504893521031497 22679717697378670140773623)
            ·
              refine ⟨34019576546068005211160435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22679717697378670140773623 34019576546068005211160435)
              ·
                refine ⟨51029364819102007816740653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34019576546068005211160435 51029364819102007816740653)
                ·
                  refine ⟨19136011807163252931277745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51029364819102007816740653 19136011807163252931277745)
                  ·
                    refine ⟨14352008855372439698458309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19136011807163252931277745 14352008855372439698458309)
                    ·
                      refine ⟨2691001660382332443460933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14352008855372439698458309 2691001660382332443460933)
                      ·
                        rfl

theorem cell23_5240707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_5240707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240707 prefixEnd_5240707 := by exact prefixLift 5240707
  have htrace : WordTrace (prefixWord ++ tailWord_5240707) baseStart_5240707 baseEnd_5240707 := by
    simpa [prefixWord, tailWord_5240707, baseEnd_5240707] using wordTrace_append hprefix tailTrace_5240707
  have hstable : (prefixWord ++ tailWord_5240707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240707).length < 2 ^ (prefixWord ++ tailWord_5240707).sum := by decide
  have hdescent : baseEnd_5240707 < baseStart_5240707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240722 : List Nat := [3, 2, 3, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_5240722 : Nat := 118140960795 + 5240722 * 2 ^ 59
def prefixEnd_5240722 : Nat := 4983230072969 + 3 ^ 40 * 5240722 * 2
def baseEnd_5240722 : Nat := 2691009362592149884773365

theorem tailTrace_5240722 : CollatzResearch.WordTrace tailWord_5240722 prefixEnd_5240722 2691009362592149884773365 := by
  unfold tailWord_5240722
  simp only [CollatzResearch.WordTrace]
  refine ⟨47786208629941678226153105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127429889679844475269741613 47786208629941678226153105)
  ·
    refine ⟨35839656472456258669614829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47786208629941678226153105 35839656472456258669614829)
    ·
      refine ⟨13439871177171097001105561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35839656472456258669614829 13439871177171097001105561)
      ·
        refine ⟨10079903382878322750829171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13439871177171097001105561 10079903382878322750829171)
        ·
          refine ⟨15119855074317484126243757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10079903382878322750829171 15119855074317484126243757)
          ·
            refine ⟨5669945652869056547341409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15119855074317484126243757 5669945652869056547341409)
            ·
              refine ⟨4252459239651792410506057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5669945652869056547341409 4252459239651792410506057)
              ·
                refine ⟨3189344429738844307879543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4252459239651792410506057 3189344429738844307879543)
                ·
                  refine ⟨4784016644608266461819315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189344429738844307879543 4784016644608266461819315)
                  ·
                    refine ⟨7176024966912399692728973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4784016644608266461819315 7176024966912399692728973)
                    ·
                      refine ⟨2691009362592149884773365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7176024966912399692728973 2691009362592149884773365)
                      ·
                        rfl

theorem cell23_5240722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_5240722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240722 prefixEnd_5240722 := by exact prefixLift 5240722
  have htrace : WordTrace (prefixWord ++ tailWord_5240722) baseStart_5240722 baseEnd_5240722 := by
    simpa [prefixWord, tailWord_5240722, baseEnd_5240722] using wordTrace_append hprefix tailTrace_5240722
  have hstable : (prefixWord ++ tailWord_5240722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240722).length < 2 ^ (prefixWord ++ tailWord_5240722).sum := by decide
  have hdescent : baseEnd_5240722 < baseStart_5240722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240784 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 3, 4, 2]
def baseStart_5240784 : Nat := 118140960795 + 5240784 * 2 ^ 59
def prefixEnd_5240784 : Nat := 4983230072969 + 3 ^ 40 * 5240784 * 2
def baseEnd_5240784 : Nat := 2691041198392728642198079

theorem tailTrace_5240784 : CollatzResearch.WordTrace tailWord_5240784 prefixEnd_5240784 2691041198392728642198079 := by
  unfold tailWord_5240784
  simp only [CollatzResearch.WordTrace]
  refine ⟨95573547922771048746684703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127431397230361398328912937 95573547922771048746684703)
  ·
    refine ⟨143360321884156573120027055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95573547922771048746684703 143360321884156573120027055)
    ·
      refine ⟨215040482826234859680040583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143360321884156573120027055 215040482826234859680040583)
      ·
        refine ⟨322560724239352289520060875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215040482826234859680040583 322560724239352289520060875)
        ·
          refine ⟨483841086359028434280091313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322560724239352289520060875 483841086359028434280091313)
          ·
            refine ⟨362880814769271325710068485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483841086359028434280091313 362880814769271325710068485)
            ·
              refine ⟨68040152769238373570637841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 362880814769271325710068485 68040152769238373570637841)
              ·
                refine ⟨51030114576928780177978381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68040152769238373570637841 51030114576928780177978381)
                ·
                  refine ⟨19136292966348292566741893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51030114576928780177978381 19136292966348292566741893)
                  ·
                    refine ⟨3588054931190304856264105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19136292966348292566741893 3588054931190304856264105)
                    ·
                      refine ⟨2691041198392728642198079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588054931190304856264105 2691041198392728642198079)
                      ·
                        rfl

theorem cell23_5240784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 4, 2].length) (baseStart_5240784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240784 prefixEnd_5240784 := by exact prefixLift 5240784
  have htrace : WordTrace (prefixWord ++ tailWord_5240784) baseStart_5240784 baseEnd_5240784 := by
    simpa [prefixWord, tailWord_5240784, baseEnd_5240784] using wordTrace_append hprefix tailTrace_5240784
  have hstable : (prefixWord ++ tailWord_5240784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240784).length < 2 ^ (prefixWord ++ tailWord_5240784).sum := by decide
  have hdescent : baseEnd_5240784 < baseStart_5240784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240801 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 1, 4, 2]
def baseStart_5240801 : Nat := 118140960795 + 5240801 * 2 ^ 59
def prefixEnd_5240801 : Nat := 4983230072969 + 3 ^ 40 * 5240801 * 2
def baseEnd_5240801 : Nat := 2691049927563855075685501

theorem tailTrace_5240801 : CollatzResearch.WordTrace tailWord_5240801 prefixEnd_5240801 2691049927563855075685501 := by
  unfold tailWord_5240801
  simp only [CollatzResearch.WordTrace]
  refine ⟨191147715886480509396738257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127431810590987006264492171 191147715886480509396738257)
  ·
    refine ⟨143360786914860382047553693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191147715886480509396738257 143360786914860382047553693)
    ·
      refine ⟨53760295093072643267832635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143360786914860382047553693 53760295093072643267832635)
      ·
        refine ⟨80640442639608964901748953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53760295093072643267832635 80640442639608964901748953)
        ·
          refine ⟨60480331979706723676311715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80640442639608964901748953 60480331979706723676311715)
          ·
            refine ⟨90720497969560085514467573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60480331979706723676311715 90720497969560085514467573)
            ·
              refine ⟨8505046684646258016981335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90720497969560085514467573 8505046684646258016981335)
              ·
                refine ⟨12757570026969387025472003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8505046684646258016981335 12757570026969387025472003)
                ·
                  refine ⟨19136355040454080538208005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12757570026969387025472003 19136355040454080538208005)
                  ·
                    refine ⟨3588066570085140100914001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19136355040454080538208005 3588066570085140100914001)
                    ·
                      refine ⟨2691049927563855075685501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588066570085140100914001 2691049927563855075685501)
                      ·
                        rfl

theorem cell23_5240801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_5240801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240801 prefixEnd_5240801 := by exact prefixLift 5240801
  have htrace : WordTrace (prefixWord ++ tailWord_5240801) baseStart_5240801 baseEnd_5240801 := by
    simpa [prefixWord, tailWord_5240801, baseEnd_5240801] using wordTrace_append hprefix tailTrace_5240801
  have hstable : (prefixWord ++ tailWord_5240801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240801).length < 2 ^ (prefixWord ++ tailWord_5240801).sum := by decide
  have hdescent : baseEnd_5240801 < baseStart_5240801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240925 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_5240925 : Nat := 118140960795 + 5240925 * 2 ^ 59
def prefixEnd_5240925 : Nat := 4983230072969 + 3 ^ 40 * 5240925 * 2
def baseEnd_5240925 : Nat := 2691113599165012590534931

theorem tailTrace_5240925 : CollatzResearch.WordTrace tailWord_5240925 prefixEnd_5240925 2691113599165012590534931 := by
  unfold tailWord_5240925
  simp only [CollatzResearch.WordTrace]
  refine ⟨191152238538031278574252229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127434825692020852382834819 191152238538031278574252229)
  ·
    refine ⟨35841044725880864732672293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191152238538031278574252229 35841044725880864732672293)
    ·
      refine ⟨6720195886102662137376055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35841044725880864732672293 6720195886102662137376055)
      ·
        refine ⟨10080293829153993206064083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6720195886102662137376055 10080293829153993206064083)
        ·
          refine ⟨15120440743730989809096125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10080293829153993206064083 15120440743730989809096125)
          ·
            refine ⟨5670165278899121178411047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15120440743730989809096125 5670165278899121178411047)
            ·
              refine ⟨8505247918348681767616571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5670165278899121178411047 8505247918348681767616571)
              ·
                refine ⟨12757871877523022651424857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8505247918348681767616571 12757871877523022651424857)
                ·
                  refine ⟨9568403908142266988568643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12757871877523022651424857 9568403908142266988568643)
                  ·
                    refine ⟨14352605862213400482852965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9568403908142266988568643 14352605862213400482852965)
                    ·
                      refine ⟨2691113599165012590534931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14352605862213400482852965 2691113599165012590534931)
                      ·
                        rfl

theorem cell23_5240925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_5240925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240925 prefixEnd_5240925 := by exact prefixLift 5240925
  have htrace : WordTrace (prefixWord ++ tailWord_5240925) baseStart_5240925 baseEnd_5240925 := by
    simpa [prefixWord, tailWord_5240925, baseEnd_5240925] using wordTrace_append hprefix tailTrace_5240925
  have hstable : (prefixWord ++ tailWord_5240925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240925).length < 2 ^ (prefixWord ++ tailWord_5240925).sum := by decide
  have hdescent : baseEnd_5240925 < baseStart_5240925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240928 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 3]
def baseStart_5240928 : Nat := 118140960795 + 5240928 * 2 ^ 59
def prefixEnd_5240928 : Nat := 4983230072969 + 3 ^ 40 * 5240928 * 2
def baseEnd_5240928 : Nat := 2691115139606976078797417

theorem tailTrace_5240928 : CollatzResearch.WordTrace tailWord_5240928 prefixEnd_5240928 2691115139606976078797417 := by
  unfold tailWord_5240928
  simp only [CollatzResearch.WordTrace]
  refine ⟨95576173978510205043305719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127434898638013606724407625 95576173978510205043305719)
  ·
    refine ⟨143364260967765307564958579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95576173978510205043305719 143364260967765307564958579)
    ·
      refine ⟨215046391451647961347437869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143364260967765307564958579 215046391451647961347437869)
      ·
        refine ⟨80642396794367985505289201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215046391451647961347437869 80642396794367985505289201)
        ·
          refine ⟨60481797595775989128966901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80642396794367985505289201 60481797595775989128966901)
          ·
            refine ⟨5670168524603998980840647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60481797595775989128966901 5670168524603998980840647)
            ·
              refine ⟨8505252786905998471260971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5670168524603998980840647 8505252786905998471260971)
              ·
                refine ⟨12757879180358997706891457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8505252786905998471260971 12757879180358997706891457)
                ·
                  refine ⟨9568409385269248280168593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12757879180358997706891457 9568409385269248280168593)
                  ·
                    refine ⟨7176307038951936210126445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9568409385269248280168593 7176307038951936210126445)
                    ·
                      refine ⟨2691115139606976078797417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7176307038951936210126445 2691115139606976078797417)
                      ·
                        rfl

theorem cell23_5240928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_5240928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240928 prefixEnd_5240928 := by exact prefixLift 5240928
  have htrace : WordTrace (prefixWord ++ tailWord_5240928) baseStart_5240928 baseEnd_5240928 := by
    simpa [prefixWord, tailWord_5240928, baseEnd_5240928] using wordTrace_append hprefix tailTrace_5240928
  have hstable : (prefixWord ++ tailWord_5240928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240928).length < 2 ^ (prefixWord ++ tailWord_5240928).sum := by decide
  have hdescent : baseEnd_5240928 < baseStart_5240928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240968 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 1, 5, 2]
def baseStart_5240968 : Nat := 118140960795 + 5240968 * 2 ^ 59
def prefixEnd_5240968 : Nat := 4983230072969 + 3 ^ 40 * 5240968 * 2
def baseEnd_5240968 : Nat := 2691135678833155922297233

theorem tailTrace_5240968 : CollatzResearch.WordTrace tailWord_5240968 prefixEnd_5240968 2691135678833155922297233 := by
  unfold tailWord_5240968
  simp only [CollatzResearch.WordTrace]
  refine ⟨95576903438437748459033779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127435871251250331278711705 95576903438437748459033779)
  ·
    refine ⟨143365355157656622688550669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95576903438437748459033779 143365355157656622688550669)
    ·
      refine ⟨53762008184121233508206501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143365355157656622688550669 53762008184121233508206501)
      ·
        refine ⟨10080376534522731282788719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53762008184121233508206501 10080376534522731282788719)
        ·
          refine ⟨15120564801784096924183079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10080376534522731282788719 15120564801784096924183079)
          ·
            refine ⟨22680847202676145386274619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15120564801784096924183079 22680847202676145386274619)
            ·
              refine ⟨34021270804014218079411929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22680847202676145386274619 34021270804014218079411929)
              ·
                refine ⟨25515953103010663559558947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34021270804014218079411929 25515953103010663559558947)
                ·
                  refine ⟨38273929654515995339338421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25515953103010663559558947 38273929654515995339338421)
                  ·
                    refine ⟨3588180905110874563062977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38273929654515995339338421 3588180905110874563062977)
                    ·
                      refine ⟨2691135678833155922297233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588180905110874563062977 2691135678833155922297233)
                      ·
                        rfl

theorem cell23_5240968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_5240968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240968 prefixEnd_5240968 := by exact prefixLift 5240968
  have htrace : WordTrace (prefixWord ++ tailWord_5240968) baseStart_5240968 baseEnd_5240968 := by
    simpa [prefixWord, tailWord_5240968, baseEnd_5240968] using wordTrace_append hprefix tailTrace_5240968
  have hstable : (prefixWord ++ tailWord_5240968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240968).length < 2 ^ (prefixWord ++ tailWord_5240968).sum := by decide
  have hdescent : baseEnd_5240968 < baseStart_5240968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240978 : List Nat := [3, 2, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_5240978 : Nat := 118140960795 + 5240978 * 2 ^ 59
def prefixEnd_5240978 : Nat := 4983230072969 + 3 ^ 40 * 5240978 * 2
def baseEnd_5240978 : Nat := 897046937879900294390729

theorem tailTrace_5240978 : CollatzResearch.WordTrace tailWord_5240978 prefixEnd_5240978 897046937879900294390729 := by
  unfold tailWord_5240978
  simp only [CollatzResearch.WordTrace]
  refine ⟨47788542901709817156482897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127436114404559512417287725 47788542901709817156482897)
  ·
    refine ⟨35841407176282362867362173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47788542901709817156482897 35841407176282362867362173)
    ·
      refine ⟨13440527691105886075260815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35841407176282362867362173 13440527691105886075260815)
      ·
        refine ⟨20160791536658829112891223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13440527691105886075260815 20160791536658829112891223)
        ·
          refine ⟨30241187304988243669336835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20160791536658829112891223 30241187304988243669336835)
          ·
            refine ⟨45361780957482365504005253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30241187304988243669336835 45361780957482365504005253)
            ·
              refine ⟨8505333929527943532000985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45361780957482365504005253 8505333929527943532000985)
              ·
                refine ⟨6379000447145957649000739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8505333929527943532000985 6379000447145957649000739)
                ·
                  refine ⟨9568500670718936473501109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6379000447145957649000739 9568500670718936473501109)
                  ·
                    refine ⟨897046937879900294390729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9568500670718936473501109 897046937879900294390729)
                    ·
                      rfl

theorem cell23_5240978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_5240978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240978 prefixEnd_5240978 := by exact prefixLift 5240978
  have htrace : WordTrace (prefixWord ++ tailWord_5240978) baseStart_5240978 baseEnd_5240978 := by
    simpa [prefixWord, tailWord_5240978, baseEnd_5240978] using wordTrace_append hprefix tailTrace_5240978
  have hstable : (prefixWord ++ tailWord_5240978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240978).length < 2 ^ (prefixWord ++ tailWord_5240978).sum := by decide
  have hdescent : baseEnd_5240978 < baseStart_5240978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240981 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 2, 6, 2]
def baseStart_5240981 : Nat := 118140960795 + 5240981 * 2 ^ 59
def prefixEnd_5240981 : Nat := 4983230072969 + 3 ^ 40 * 5240981 * 2
def baseEnd_5240981 : Nat := 2691142354081664371434673

theorem tailTrace_5240981 : CollatzResearch.WordTrace tailWord_5240981 prefixEnd_5240981 2691142354081664371434673 := by
  unfold tailWord_5240981
  simp only [CollatzResearch.WordTrace]
  refine ⟨191154281025828400138290797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127436187350552266758860531 191154281025828400138290797)
  ·
    refine ⟨71682855384685650051859049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191154281025828400138290797 71682855384685650051859049)
    ·
      refine ⟨53762141538514237538894287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71682855384685650051859049 53762141538514237538894287)
      ·
        refine ⟨80643212307771356308341431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53762141538514237538894287 80643212307771356308341431)
        ·
          refine ⟨120964818461657034462512147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80643212307771356308341431 120964818461657034462512147)
          ·
            refine ⟨181447227692485551693768221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120964818461657034462512147 181447227692485551693768221)
            ·
              refine ⟨68042710384682081885163083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181447227692485551693768221 68042710384682081885163083)
              ·
                refine ⟨102064065577023122827744625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68042710384682081885163083 102064065577023122827744625)
                ·
                  refine ⟨76548049182767342120808469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102064065577023122827744625 76548049182767342120808469)
                  ·
                    refine ⟨3588189805442219161912897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76548049182767342120808469 3588189805442219161912897)
                    ·
                      refine ⟨2691142354081664371434673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588189805442219161912897 2691142354081664371434673)
                      ·
                        rfl

theorem cell23_5240981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_5240981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240981 prefixEnd_5240981 := by exact prefixLift 5240981
  have htrace : WordTrace (prefixWord ++ tailWord_5240981) baseStart_5240981 baseEnd_5240981 := by
    simpa [prefixWord, tailWord_5240981, baseEnd_5240981] using wordTrace_append hprefix tailTrace_5240981
  have hstable : (prefixWord ++ tailWord_5240981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240981).length < 2 ^ (prefixWord ++ tailWord_5240981).sum := by decide
  have hdescent : baseEnd_5240981 < baseStart_5240981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5240992 : List Nat := [2, 1, 1, 4, 2, 4, 1, 3, 1, 1, 3]
def baseStart_5240992 : Nat := 118140960795 + 5240992 * 2 ^ 59
def prefixEnd_5240992 : Nat := 4983230072969 + 3 ^ 40 * 5240992 * 2
def baseEnd_5240992 : Nat := 2691148002368863828397123

theorem tailTrace_5240992 : CollatzResearch.WordTrace tailWord_5240992 prefixEnd_5240992 2691148002368863828397123 := by
  unfold tailWord_5240992
  simp only [CollatzResearch.WordTrace]
  refine ⟨95577341114394274508470615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127436454819192366011294153 95577341114394274508470615)
  ·
    refine ⟨143366011671591411762705923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95577341114394274508470615 143366011671591411762705923)
    ·
      refine ⟨215049017507387117644058885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143366011671591411762705923 215049017507387117644058885)
      ·
        refine ⟨40321690782635084558261041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215049017507387117644058885 40321690782635084558261041)
        ·
          refine ⟨30241268086976313418695781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40321690782635084558261041 30241268086976313418695781)
          ·
            refine ⟨5670237766308058766005459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30241268086976313418695781 5670237766308058766005459)
            ·
              refine ⟨8505356649462088149008189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5670237766308058766005459 8505356649462088149008189)
              ·
                refine ⟨3189508743548283055878071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8505356649462088149008189 3189508743548283055878071)
                ·
                  refine ⟨4784263115322424583817107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189508743548283055878071 4784263115322424583817107)
                  ·
                    refine ⟨7176394672983636875725661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4784263115322424583817107 7176394672983636875725661)
                    ·
                      refine ⟨2691148002368863828397123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7176394672983636875725661 2691148002368863828397123)
                      ·
                        rfl

theorem cell23_5240992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_5240992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5240992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5240992 prefixEnd_5240992 := by exact prefixLift 5240992
  have htrace : WordTrace (prefixWord ++ tailWord_5240992) baseStart_5240992 baseEnd_5240992 := by
    simpa [prefixWord, tailWord_5240992, baseEnd_5240992] using wordTrace_append hprefix tailTrace_5240992
  have hstable : (prefixWord ++ tailWord_5240992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5240992).length < 2 ^ (prefixWord ++ tailWord_5240992).sum := by decide
  have hdescent : baseEnd_5240992 < baseStart_5240992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5240992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241002 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_5241002 : Nat := 118140960795 + 5241002 * 2 ^ 59
def prefixEnd_5241002 : Nat := 4983230072969 + 3 ^ 40 * 5241002 * 2
def baseEnd_5241002 : Nat := 2691153137175408789272077

theorem tailTrace_5241002 : CollatzResearch.WordTrace tailWord_5241002 prefixEnd_5241002 2691153137175408789272077 := by
  unfold tailWord_5241002
  simp only [CollatzResearch.WordTrace]
  refine ⟨47788761739688080181201315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127436697972501547149870173 47788761739688080181201315)
  ·
    refine ⟨71683142609532120271801973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47788761739688080181201315 71683142609532120271801973)
    ·
      refine ⟨6720294619643636275481435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71683142609532120271801973 6720294619643636275481435)
      ·
        refine ⟨10080441929465454413222153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6720294619643636275481435 10080441929465454413222153)
        ·
          refine ⟨7560331447099090809916615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10080441929465454413222153 7560331447099090809916615)
          ·
            refine ⟨11340497170648636214874923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7560331447099090809916615 11340497170648636214874923)
            ·
              refine ⟨17010745755972954322312385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11340497170648636214874923 17010745755972954322312385)
              ·
                refine ⟨12758059316979715741734289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17010745755972954322312385 12758059316979715741734289)
                ·
                  refine ⟨9568544487734786806300717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12758059316979715741734289 9568544487734786806300717)
                  ·
                    refine ⟨3588204182900545052362769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9568544487734786806300717 3588204182900545052362769)
                    ·
                      refine ⟨2691153137175408789272077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588204182900545052362769 2691153137175408789272077)
                      ·
                        rfl

theorem cell23_5241002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_5241002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241002 prefixEnd_5241002 := by exact prefixLift 5241002
  have htrace : WordTrace (prefixWord ++ tailWord_5241002) baseStart_5241002 baseEnd_5241002 := by
    simpa [prefixWord, tailWord_5241002, baseEnd_5241002] using wordTrace_append hprefix tailTrace_5241002
  have hstable : (prefixWord ++ tailWord_5241002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241002).length < 2 ^ (prefixWord ++ tailWord_5241002).sum := by decide
  have hdescent : baseEnd_5241002 < baseStart_5241002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241009 : List Nat := [1, 2, 2, 5, 2, 1, 3, 2, 1, 1, 3]
def baseStart_5241009 : Nat := 118140960795 + 5241009 * 2 ^ 59
def prefixEnd_5241009 : Nat := 4983230072969 + 3 ^ 40 * 5241009 * 2
def baseEnd_5241009 : Nat := 2691156731539990261884545

theorem tailTrace_5241009 : CollatzResearch.WordTrace tailWord_5241009 prefixEnd_5241009 2691156731539990261884545 := by
  unfold tailWord_5241009
  simp only [CollatzResearch.WordTrace]
  refine ⟨191155302269726960920310081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127436868179817973946873387 191155302269726960920310081)
  ·
    refine ⟨143366476702295220690232561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191155302269726960920310081 143366476702295220690232561)
    ·
      refine ⟨107524857526721415517674421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143366476702295220690232561 107524857526721415517674421)
      ·
        refine ⟨10080455393130132704781977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107524857526721415517674421 10080455393130132704781977)
        ·
          refine ⟨7560341544847599528586483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10080455393130132704781977 7560341544847599528586483)
          ·
            refine ⟨11340512317271399292879725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7560341544847599528586483 11340512317271399292879725)
            ·
              refine ⟨4252692118976774734829897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11340512317271399292879725 4252692118976774734829897)
              ·
                refine ⟨3189519089232581051122423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4252692118976774734829897 3189519089232581051122423)
                ·
                  refine ⟨4784278633848871576683635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189519089232581051122423 4784278633848871576683635)
                  ·
                    refine ⟨7176417950773307365025453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4784278633848871576683635 7176417950773307365025453)
                    ·
                      refine ⟨2691156731539990261884545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7176417950773307365025453 2691156731539990261884545)
                      ·
                        rfl

theorem cell23_5241009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_5241009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241009 prefixEnd_5241009 := by exact prefixLift 5241009
  have htrace : WordTrace (prefixWord ++ tailWord_5241009) baseStart_5241009 baseEnd_5241009 := by
    simpa [prefixWord, tailWord_5241009, baseEnd_5241009] using wordTrace_append hprefix tailTrace_5241009
  have hstable : (prefixWord ++ tailWord_5241009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241009).length < 2 ^ (prefixWord ++ tailWord_5241009).sum := by decide
  have hdescent : baseEnd_5241009 < baseStart_5241009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241015 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 3, 2, 2]
def baseStart_5241015 : Nat := 118140960795 + 5241015 * 2 ^ 59
def prefixEnd_5241015 : Nat := 4983230072969 + 3 ^ 40 * 5241015 * 2
def baseEnd_5241015 : Nat := 2691159812423917238409517

theorem tailTrace_5241015 : CollatzResearch.WordTrace tailWord_5241015 prefixEnd_5241015 2691159812423917238409517 := by
  unfold tailWord_5241015
  simp only [CollatzResearch.WordTrace]
  refine ⟨191155521107705223945028499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127437014071803482630018999 191155521107705223945028499)
  ·
    refine ⟨286733281661557835917542749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191155521107705223945028499 286733281661557835917542749)
    ·
      refine ⟨107524980623084188469078531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286733281661557835917542749 107524980623084188469078531)
      ·
        refine ⟨161287470934626282703617797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107524980623084188469078531 161287470934626282703617797)
        ·
          refine ⟨30241400800242428006928337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161287470934626282703617797 30241400800242428006928337)
          ·
            refine ⟨22681050600181821005196253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30241400800242428006928337 22681050600181821005196253)
            ·
              refine ⟨8505393975068182876948595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22681050600181821005196253 8505393975068182876948595)
              ·
                refine ⟨12758090962602274315422893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8505393975068182876948595 12758090962602274315422893)
                ·
                  refine ⟨4784284110975852868283585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12758090962602274315422893 4784284110975852868283585)
                  ·
                    refine ⟨3588213083231889651212689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4784284110975852868283585 3588213083231889651212689)
                    ·
                      refine ⟨2691159812423917238409517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588213083231889651212689 2691159812423917238409517)
                      ·
                        rfl

theorem cell23_5241015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 2, 2].length) (baseStart_5241015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241015 prefixEnd_5241015 := by exact prefixLift 5241015
  have htrace : WordTrace (prefixWord ++ tailWord_5241015) baseStart_5241015 baseEnd_5241015 := by
    simpa [prefixWord, tailWord_5241015, baseEnd_5241015] using wordTrace_append hprefix tailTrace_5241015
  have hstable : (prefixWord ++ tailWord_5241015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241015).length < 2 ^ (prefixWord ++ tailWord_5241015).sum := by decide
  have hdescent : baseEnd_5241015 < baseStart_5241015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241048 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 1, 3, 3]
def baseStart_5241048 : Nat := 118140960795 + 5241048 * 2 ^ 59
def prefixEnd_5241048 : Nat := 4983230072969 + 3 ^ 40 * 5241048 * 2
def baseEnd_5241048 : Nat := 2691176757285515609296865

theorem tailTrace_5241048 : CollatzResearch.WordTrace tailWord_5241048 prefixEnd_5241048 2691176757285515609296865 := by
  unfold tailWord_5241048
  simp only [CollatzResearch.WordTrace]
  refine ⟨95578362358292835290489899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127437816477723780387319865 95578362358292835290489899)
  ·
    refine ⟨143367543537439252935734849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95578362358292835290489899 143367543537439252935734849)
    ·
      refine ⟨107525657653079439701801137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143367543537439252935734849 107525657653079439701801137)
      ·
        refine ⟨80644243239809579776350853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107525657653079439701801137 80644243239809579776350853)
        ·
          refine ⟨15120795607464296208065785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80644243239809579776350853 15120795607464296208065785)
          ·
            refine ⟨11340596705598222156049339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15120795607464296208065785 11340596705598222156049339)
            ·
              refine ⟨17010895058397333234074009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11340596705598222156049339 17010895058397333234074009)
              ·
                refine ⟨12758171293797999925555507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17010895058397333234074009 12758171293797999925555507)
                ·
                  refine ⟨19137256940696999888333261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12758171293797999925555507 19137256940696999888333261)
                  ·
                    refine ⟨7176471352761374958124973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19137256940696999888333261 7176471352761374958124973)
                    ·
                      refine ⟨2691176757285515609296865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7176471352761374958124973 2691176757285515609296865)
                      ·
                        rfl

theorem cell23_5241048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_5241048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241048 prefixEnd_5241048 := by exact prefixLift 5241048
  have htrace : WordTrace (prefixWord ++ tailWord_5241048) baseStart_5241048 baseEnd_5241048 := by
    simpa [prefixWord, tailWord_5241048, baseEnd_5241048] using wordTrace_append hprefix tailTrace_5241048
  have hstable : (prefixWord ++ tailWord_5241048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241048).length < 2 ^ (prefixWord ++ tailWord_5241048).sum := by decide
  have hdescent : baseEnd_5241048 < baseStart_5241048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241052 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5241052 : Nat := 118140960795 + 5241052 * 2 ^ 59
def prefixEnd_5241052 : Nat := 4983230072969 + 3 ^ 40 * 5241052 * 2
def baseEnd_5241052 : Nat := 2691178811208133593646847

theorem tailTrace_5241052 : CollatzResearch.WordTrace tailWord_5241052 prefixEnd_5241052 2691178811208133593646847 := by
  unfold tailWord_5241052
  simp only [CollatzResearch.WordTrace]
  refine ⟨95578435304285589632062705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127437913739047452842750273 95578435304285589632062705)
  ·
    refine ⟨71683826478214192224047029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95578435304285589632062705 71683826478214192224047029)
    ·
      refine ⟨6720358732332580521004409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71683826478214192224047029 6720358732332580521004409)
      ·
        refine ⟨5040269049249435390753307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6720358732332580521004409 5040269049249435390753307)
        ·
          refine ⟨7560403573874153086129961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5040269049249435390753307 7560403573874153086129961)
          ·
            refine ⟨5670302680405614814597471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7560403573874153086129961 5670302680405614814597471)
            ·
              refine ⟨8505454020608422221896207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5670302680405614814597471 8505454020608422221896207)
              ·
                refine ⟨12758181030912633332844311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8505454020608422221896207 12758181030912633332844311)
                ·
                  refine ⟨19137271546368949999266467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12758181030912633332844311 19137271546368949999266467)
                  ·
                    refine ⟨28705907319553424998899701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19137271546368949999266467 28705907319553424998899701)
                    ·
                      refine ⟨2691178811208133593646847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28705907319553424998899701 2691178811208133593646847)
                      ·
                        rfl

theorem cell23_5241052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5241052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241052 prefixEnd_5241052 := by exact prefixLift 5241052
  have htrace : WordTrace (prefixWord ++ tailWord_5241052) baseStart_5241052 baseEnd_5241052 := by
    simpa [prefixWord, tailWord_5241052, baseEnd_5241052] using wordTrace_append hprefix tailTrace_5241052
  have hstable : (prefixWord ++ tailWord_5241052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241052).length < 2 ^ (prefixWord ++ tailWord_5241052).sum := by decide
  have hdescent : baseEnd_5241052 < baseStart_5241052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241071 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 4]
def baseStart_5241071 : Nat := 118140960795 + 5241071 * 2 ^ 59
def prefixEnd_5241071 : Nat := 4983230072969 + 3 ^ 40 * 5241071 * 2
def baseEnd_5241071 : Nat := 2691188567340569019309259

theorem tailTrace_5241071 : CollatzResearch.WordTrace tailWord_5241071 prefixEnd_5241071 2691188567340569019309259 := by
  unfold tailWord_5241071
  simp only [CollatzResearch.WordTrace]
  refine ⟨191157563595502345509067067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127438375730334897006044711 191157563595502345509067067)
  ·
    refine ⟨286736345393253518263600601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191157563595502345509067067 286736345393253518263600601)
    ·
      refine ⟨215052259044940138697700451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286736345393253518263600601 215052259044940138697700451)
      ·
        refine ⟨322578388567410208046550677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215052259044940138697700451 322578388567410208046550677)
        ·
          refine ⟨15120861964097353502182063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 322578388567410208046550677 15120861964097353502182063)
          ·
            refine ⟨22681292946146030253273095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15120861964097353502182063 22681292946146030253273095)
            ·
              refine ⟨34021939419219045379909643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22681292946146030253273095 34021939419219045379909643)
              ·
                refine ⟨51032909128828568069864465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34021939419219045379909643 51032909128828568069864465)
                ·
                  refine ⟨38274681846621426052398349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51032909128828568069864465 38274681846621426052398349)
                  ·
                    refine ⟨14353005692483034769649381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38274681846621426052398349 14353005692483034769649381)
                    ·
                      refine ⟨2691188567340569019309259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14353005692483034769649381 2691188567340569019309259)
                      ·
                        rfl

theorem cell23_5241071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_5241071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241071 prefixEnd_5241071 := by exact prefixLift 5241071
  have htrace : WordTrace (prefixWord ++ tailWord_5241071) baseStart_5241071 baseEnd_5241071 := by
    simpa [prefixWord, tailWord_5241071, baseEnd_5241071] using wordTrace_append hprefix tailTrace_5241071
  have hstable : (prefixWord ++ tailWord_5241071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241071).length < 2 ^ (prefixWord ++ tailWord_5241071).sum := by decide
  have hdescent : baseEnd_5241071 < baseStart_5241071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241088 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 1, 4, 2]
def baseStart_5241088 : Nat := 118140960795 + 5241088 * 2 ^ 59
def prefixEnd_5241088 : Nat := 4983230072969 + 3 ^ 40 * 5241088 * 2
def baseEnd_5241088 : Nat := 2691197296511695452796681

theorem tailTrace_5241088 : CollatzResearch.WordTrace tailWord_5241088 prefixEnd_5241088 2691197296511695452796681 := by
  unfold tailWord_5241088
  simp only [CollatzResearch.WordTrace]
  refine ⟨95579091818220378706217959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127438789090960504941623945 95579091818220378706217959)
  ·
    refine ⟨143368637727330568059326939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95579091818220378706217959 143368637727330568059326939)
    ·
      refine ⟨215052956590995852088990409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143368637727330568059326939 215052956590995852088990409)
      ·
        refine ⟨161289717443246889066742807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215052956590995852088990409 161289717443246889066742807)
        ·
          refine ⟨241934576164870333600114211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161289717443246889066742807 241934576164870333600114211)
          ·
            refine ⟨362901864247305500400171317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241934576164870333600114211 362901864247305500400171317)
            ·
              refine ⟨34022049773184890662516061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 362901864247305500400171317 34022049773184890662516061)
              ·
                refine ⟨12758268664944333998443523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34022049773184890662516061 12758268664944333998443523)
                ·
                  refine ⟨19137402997416500997665285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12758268664944333998443523 19137402997416500997665285)
                  ·
                    refine ⟨3588263062015593937062241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19137402997416500997665285 3588263062015593937062241)
                    ·
                      refine ⟨2691197296511695452796681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588263062015593937062241 2691197296511695452796681)
                      ·
                        rfl

theorem cell23_5241088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 4, 2].length) (baseStart_5241088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241088 prefixEnd_5241088 := by exact prefixLift 5241088
  have htrace : WordTrace (prefixWord ++ tailWord_5241088) baseStart_5241088 baseEnd_5241088 := by
    simpa [prefixWord, tailWord_5241088, baseEnd_5241088] using wordTrace_append hprefix tailTrace_5241088
  have hstable : (prefixWord ++ tailWord_5241088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241088).length < 2 ^ (prefixWord ++ tailWord_5241088).sum := by decide
  have hdescent : baseEnd_5241088 < baseStart_5241088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241091 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 3]
def baseStart_5241091 : Nat := 118140960795 + 5241091 * 2 ^ 59
def prefixEnd_5241091 : Nat := 4983230072969 + 3 ^ 40 * 5241091 * 2
def baseEnd_5241091 : Nat := 2691198836953658941059167

theorem tailTrace_5241091 : CollatzResearch.WordTrace tailWord_5241091 prefixEnd_5241091 2691198836953658941059167 := by
  unfold tailWord_5241091
  simp only [CollatzResearch.WordTrace]
  refine ⟨191158293055429888924795127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127438862036953259283196751 191158293055429888924795127)
  ·
    refine ⟨286737439583144833387192691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191158293055429888924795127 286737439583144833387192691)
    ·
      refine ⟨430106159374717250080789037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286737439583144833387192691 430106159374717250080789037)
      ·
        refine ⟨161289809765518968780295889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430106159374717250080789037 161289809765518968780295889)
        ·
          refine ⟨120967357324139226585221917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161289809765518968780295889 120967357324139226585221917)
          ·
            refine ⟨45362758996552209969458219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120967357324139226585221917 45362758996552209969458219)
            ·
              refine ⟨68044138494828314954187329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45362758996552209969458219 68044138494828314954187329)
              ·
                refine ⟨51033103871121236215640497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68044138494828314954187329 51033103871121236215640497)
                ·
                  refine ⟨38274827903340927161730373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51033103871121236215640497 38274827903340927161730373)
                  ·
                    refine ⟨7176530231876423842824445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38274827903340927161730373 7176530231876423842824445)
                    ·
                      refine ⟨2691198836953658941059167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7176530231876423842824445 2691198836953658941059167)
                      ·
                        rfl

theorem cell23_5241091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_5241091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241091 prefixEnd_5241091 := by exact prefixLift 5241091
  have htrace : WordTrace (prefixWord ++ tailWord_5241091) baseStart_5241091 baseEnd_5241091 := by
    simpa [prefixWord, tailWord_5241091, baseEnd_5241091] using wordTrace_append hprefix tailTrace_5241091
  have hstable : (prefixWord ++ tailWord_5241091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241091).length < 2 ^ (prefixWord ++ tailWord_5241091).sum := by decide
  have hdescent : baseEnd_5241091 < baseStart_5241091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241122 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_5241122 : Nat := 118140960795 + 5241122 * 2 ^ 59
def prefixEnd_5241122 : Nat := 4983230072969 + 3 ^ 40 * 5241122 * 2
def baseEnd_5241122 : Nat := 2691214754853948319771525

theorem tailTrace_5241122 : CollatzResearch.WordTrace tailWord_5241122 prefixEnd_5241122 2691214754853948319771525 := by
  unfold tailWord_5241122
  simp only [CollatzResearch.WordTrace]
  refine ⟨47789855929579395304793405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127439615812211720812782413 47789855929579395304793405)
  ·
    refine ⟨17921195973592273239297527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47789855929579395304793405 17921195973592273239297527)
    ·
      refine ⟨26881793960388409858946291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17921195973592273239297527 26881793960388409858946291)
      ·
        refine ⟨40322690940582614788419437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26881793960388409858946291 40322690940582614788419437)
        ·
          refine ⟨15121009102718480545657289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40322690940582614788419437 15121009102718480545657289)
          ·
            refine ⟨11340756827038860409242967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15121009102718480545657289 11340756827038860409242967)
            ·
              refine ⟨17011135240558290613864451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11340756827038860409242967 17011135240558290613864451)
              ·
                refine ⟨25516702860837435920796677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17011135240558290613864451 25516702860837435920796677)
                ·
                  refine ⟨4784381786407019235149377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25516702860837435920796677 4784381786407019235149377)
                  ·
                    refine ⟨3588286339805264426362033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4784381786407019235149377 3588286339805264426362033)
                    ·
                      refine ⟨2691214754853948319771525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588286339805264426362033 2691214754853948319771525)
                      ·
                        rfl

theorem cell23_5241122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_5241122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241122 prefixEnd_5241122 := by exact prefixLift 5241122
  have htrace : WordTrace (prefixWord ++ tailWord_5241122) baseStart_5241122 baseEnd_5241122 := by
    simpa [prefixWord, tailWord_5241122, baseEnd_5241122] using wordTrace_append hprefix tailTrace_5241122
  have hstable : (prefixWord ++ tailWord_5241122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241122).length < 2 ^ (prefixWord ++ tailWord_5241122).sum := by decide
  have hdescent : baseEnd_5241122 < baseStart_5241122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241141 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 3, 7]
def baseStart_5241141 : Nat := 118140960795 + 5241141 * 2 ^ 59
def prefixEnd_5241141 : Nat := 4983230072969 + 3 ^ 40 * 5241141 * 2
def baseEnd_5241141 : Nat := 897074836995461248477979

theorem tailTrace_5241141 : CollatzResearch.WordTrace tailWord_5241141 prefixEnd_5241141 897074836995461248477979 := by
  unfold tailWord_5241141
  simp only [CollatzResearch.WordTrace]
  refine ⟨191160116705248747464115277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127440077803499164976076851 191160116705248747464115277)
  ·
    refine ⟨71685043764468280299043229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191160116705248747464115277 71685043764468280299043229)
    ·
      refine ⟨26881891411675605112141211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71685043764468280299043229 26881891411675605112141211)
      ·
        refine ⟨40322837117513407668211817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26881891411675605112141211 40322837117513407668211817)
        ·
          refine ⟨30242127838135055751158863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40322837117513407668211817 30242127838135055751158863)
          ·
            refine ⟨45363191757202583626738295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30242127838135055751158863 45363191757202583626738295)
            ·
              refine ⟨68044787635803875440107443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45363191757202583626738295 68044787635803875440107443)
              ·
                refine ⟨102067181453705813160161165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68044787635803875440107443 102067181453705813160161165)
                ·
                  refine ⟨38275193045139679935060437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102067181453705813160161165 38275193045139679935060437)
                  ·
                    refine ⟨897074836995461248477979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38275193045139679935060437 897074836995461248477979)
                    ·
                      rfl

theorem cell23_5241141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_5241141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241141 prefixEnd_5241141 := by exact prefixLift 5241141
  have htrace : WordTrace (prefixWord ++ tailWord_5241141) baseStart_5241141 baseEnd_5241141 := by
    simpa [prefixWord, tailWord_5241141, baseEnd_5241141] using wordTrace_append hprefix tailTrace_5241141
  have hstable : (prefixWord ++ tailWord_5241141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241141).length < 2 ^ (prefixWord ++ tailWord_5241141).sum := by decide
  have hdescent : baseEnd_5241141 < baseStart_5241141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241221 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_5241221 : Nat := 118140960795 + 5241221 * 2 ^ 59
def prefixEnd_5241221 : Nat := 4983230072969 + 3 ^ 40 * 5241221 * 2
def baseEnd_5241221 : Nat := 2691265589438743432433569

theorem tailTrace_5241221 : CollatzResearch.WordTrace tailWord_5241221 prefixEnd_5241221 2691265589438743432433569 := by
  unfold tailWord_5241221
  simp only [CollatzResearch.WordTrace]
  refine ⟨191163034544958921127027517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127442023029972614084685011 191163034544958921127027517)
  ·
    refine ⟨71686137954359595422635319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191163034544958921127027517 71686137954359595422635319)
    ·
      refine ⟨107529206931539393133952979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71686137954359595422635319 107529206931539393133952979)
      ·
        refine ⟨161293810397309089700929469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107529206931539393133952979 161293810397309089700929469)
        ·
          refine ⟨60485178898990908637848551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161293810397309089700929469 60485178898990908637848551)
          ·
            refine ⟨90727768348486362956772827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60485178898990908637848551 90727768348486362956772827)
            ·
              refine ⟨136091652522729544435159241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90727768348486362956772827 136091652522729544435159241)
              ·
                refine ⟨102068739392047158326369431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136091652522729544435159241 102068739392047158326369431)
                ·
                  refine ⟨153103109088070737489554147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102068739392047158326369431 153103109088070737489554147)
                  ·
                    refine ⟨229654663632106106234331221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 153103109088070737489554147 229654663632106106234331221)
                    ·
                      refine ⟨2691265589438743432433569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 229654663632106106234331221 2691265589438743432433569)
                      ·
                        rfl

theorem cell23_5241221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_5241221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241221 prefixEnd_5241221 := by exact prefixLift 5241221
  have htrace : WordTrace (prefixWord ++ tailWord_5241221) baseStart_5241221 baseEnd_5241221 := by
    simpa [prefixWord, tailWord_5241221, baseEnd_5241221] using wordTrace_append hprefix tailTrace_5241221
  have hstable : (prefixWord ++ tailWord_5241221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241221).length < 2 ^ (prefixWord ++ tailWord_5241221).sum := by decide
  have hdescent : baseEnd_5241221 < baseStart_5241221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241248 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 3, 5]
def baseStart_5241248 : Nat := 118140960795 + 5241248 * 2 ^ 59
def prefixEnd_5241248 : Nat := 4983230072969 + 3 ^ 40 * 5241248 * 2
def baseEnd_5241248 : Nat := 897093151138804942265315

theorem tailTrace_5241248 : CollatzResearch.WordTrace tailWord_5241248 prefixEnd_5241248 897093151138804942265315 := by
  unfold tailWord_5241248
  simp only [CollatzResearch.WordTrace]
  refine ⟨95582009657930552369130199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127442679543907403158840265 95582009657930552369130199)
  ·
    refine ⟨143373014486895828553695299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95582009657930552369130199 143373014486895828553695299)
    ·
      refine ⟨215059521730343742830542949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143373014486895828553695299 215059521730343742830542949)
      ·
        refine ⟨40323660324439451780726803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215059521730343742830542949 40323660324439451780726803)
        ·
          refine ⟨60485490486659177671090205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40323660324439451780726803 60485490486659177671090205)
          ·
            refine ⟨22682058932497191626658827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60485490486659177671090205 22682058932497191626658827)
            ·
              refine ⟨34023088398745787439988241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22682058932497191626658827 34023088398745787439988241)
              ·
                refine ⟨25517316299059340579991181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34023088398745787439988241 25517316299059340579991181)
                ·
                  refine ⟨9568993612147252717496693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25517316299059340579991181 9568993612147252717496693)
                  ·
                    refine ⟨897093151138804942265315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9568993612147252717496693 897093151138804942265315)
                    ·
                      rfl

theorem cell23_5241248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3, 5].length) (baseStart_5241248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241248 prefixEnd_5241248 := by exact prefixLift 5241248
  have htrace : WordTrace (prefixWord ++ tailWord_5241248) baseStart_5241248 baseEnd_5241248 := by
    simpa [prefixWord, tailWord_5241248, baseEnd_5241248] using wordTrace_append hprefix tailTrace_5241248
  have hstable : (prefixWord ++ tailWord_5241248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241248).length < 2 ^ (prefixWord ++ tailWord_5241248).sum := by decide
  have hdescent : baseEnd_5241248 < baseStart_5241248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241312 : List Nat := [2, 1, 1, 3, 1, 1, 7, 1, 2, 4]
def baseStart_5241312 : Nat := 118140960795 + 5241312 * 2 ^ 59
def prefixEnd_5241312 : Nat := 4983230072969 + 3 ^ 40 * 5241312 * 2
def baseEnd_5241312 : Nat := 897104105392767525465217

theorem tailTrace_5241312 : CollatzResearch.WordTrace tailWord_5241312 prefixEnd_5241312 897104105392767525465217 := by
  unfold tailWord_5241312
  simp only [CollatzResearch.WordTrace]
  refine ⟨95583176793814621834295095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127444235725086162445726793 95583176793814621834295095)
  ·
    refine ⟨143374765190721932751442643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95583176793814621834295095 143374765190721932751442643)
    ·
      refine ⟨215062147786082899127163965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143374765190721932751442643 215062147786082899127163965)
      ·
        refine ⟨80648305419781087172686487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215062147786082899127163965 80648305419781087172686487)
        ·
          refine ⟨120972458129671630759029731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80648305419781087172686487 120972458129671630759029731)
          ·
            refine ⟨181458687194507446138544597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120972458129671630759029731 181458687194507446138544597)
            ·
              refine ⟨4252937981121268268872139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 181458687194507446138544597 4252937981121268268872139)
              ·
                refine ⟨6379406971681902403308209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4252937981121268268872139 6379406971681902403308209)
                ·
                  refine ⟨4784555228761426802481157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6379406971681902403308209 4784555228761426802481157)
                  ·
                    refine ⟨897104105392767525465217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4784555228761426802481157 897104105392767525465217)
                    ·
                      rfl

theorem cell23_5241312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 2, 4].length) (baseStart_5241312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241312 prefixEnd_5241312 := by exact prefixLift 5241312
  have htrace : WordTrace (prefixWord ++ tailWord_5241312) baseStart_5241312 baseEnd_5241312 := by
    simpa [prefixWord, tailWord_5241312, baseEnd_5241312] using wordTrace_append hprefix tailTrace_5241312
  have hstable : (prefixWord ++ tailWord_5241312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241312).length < 2 ^ (prefixWord ++ tailWord_5241312).sum := by decide
  have hdescent : baseEnd_5241312 < baseStart_5241312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241315 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 6]
def baseStart_5241315 : Nat := 118140960795 + 5241315 * 2 ^ 59
def prefixEnd_5241315 : Nat := 4983230072969 + 3 ^ 40 * 5241315 * 2
def baseEnd_5241315 : Nat := 2691313856620266064658137

theorem tailTrace_5241315 : CollatzResearch.WordTrace tailWord_5241315 prefixEnd_5241315 2691313856620266064658137 := by
  unfold tailWord_5241315
  simp only [CollatzResearch.WordTrace]
  refine ⟨191166463006618375180949399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127444308671078916787299599 191166463006618375180949399)
  ·
    refine ⟨286749694509927562771424099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191166463006618375180949399 286749694509927562771424099)
    ·
      refine ⟨430124541764891344157136149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286749694509927562771424099 430124541764891344157136149)
      ·
        refine ⟨20162087895229281757365757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 430124541764891344157136149 20162087895229281757365757)
        ·
          refine ⟨7560782960710980659012159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20162087895229281757365757 7560782960710980659012159)
          ·
            refine ⟨11341174441066470988518239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7560782960710980659012159 11341174441066470988518239)
            ·
              refine ⟨17011761661599706482777359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11341174441066470988518239 17011761661599706482777359)
              ·
                refine ⟨25517642492399559724166039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17011761661599706482777359 25517642492399559724166039)
                ·
                  refine ⟨38276463738599339586249059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25517642492399559724166039 38276463738599339586249059)
                  ·
                    refine ⟨57414695607899009379373589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38276463738599339586249059 57414695607899009379373589)
                    ·
                      refine ⟨2691313856620266064658137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57414695607899009379373589 2691313856620266064658137)
                      ·
                        rfl

theorem cell23_5241315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_5241315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241315 prefixEnd_5241315 := by exact prefixLift 5241315
  have htrace : WordTrace (prefixWord ++ tailWord_5241315) baseStart_5241315 baseEnd_5241315 := by
    simpa [prefixWord, tailWord_5241315, baseEnd_5241315] using wordTrace_append hprefix tailTrace_5241315
  have hstable : (prefixWord ++ tailWord_5241315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241315).length < 2 ^ (prefixWord ++ tailWord_5241315).sum := by decide
  have hdescent : baseEnd_5241315 < baseStart_5241315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241322 : List Nat := [3, 1, 3, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_5241322 : Nat := 118140960795 + 5241322 * 2 ^ 59
def prefixEnd_5241322 : Nat := 4983230072969 + 3 ^ 40 * 5241322 * 2
def baseEnd_5241322 : Nat := 2691317450984847537270605

theorem tailTrace_5241322 : CollatzResearch.WordTrace tailWord_5241322 prefixEnd_5241322 2691317450984847537270605 := by
  unfold tailWord_5241322
  simp only [CollatzResearch.WordTrace]
  refine ⟨47791679579398253844113555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127444478878395343584302813 47791679579398253844113555)
  ·
    refine ⟨71687519369097380766170333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47791679579398253844113555 71687519369097380766170333)
    ·
      refine ⟨26882819763411517787313875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71687519369097380766170333 26882819763411517787313875)
      ·
        refine ⟨40324229645117276680970813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26882819763411517787313875 40324229645117276680970813)
        ·
          refine ⟨15121586116918978755364055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40324229645117276680970813 15121586116918978755364055)
          ·
            refine ⟨22682379175378468133046083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15121586116918978755364055 22682379175378468133046083)
            ·
              refine ⟨34023568763067702199569125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22682379175378468133046083 34023568763067702199569125)
              ·
                refine ⟨6379419143075194162419211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34023568763067702199569125 6379419143075194162419211)
                ·
                  refine ⟨9569128714612791243628817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6379419143075194162419211 9569128714612791243628817)
                  ·
                    refine ⟨7176846535959593432721613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9569128714612791243628817 7176846535959593432721613)
                    ·
                      refine ⟨2691317450984847537270605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7176846535959593432721613 2691317450984847537270605)
                      ·
                        rfl

theorem cell23_5241322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_5241322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241322 prefixEnd_5241322 := by exact prefixLift 5241322
  have htrace : WordTrace (prefixWord ++ tailWord_5241322) baseStart_5241322 baseEnd_5241322 := by
    simpa [prefixWord, tailWord_5241322, baseEnd_5241322] using wordTrace_append hprefix tailTrace_5241322
  have hstable : (prefixWord ++ tailWord_5241322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241322).length < 2 ^ (prefixWord ++ tailWord_5241322).sum := by decide
  have hdescent : baseEnd_5241322 < baseStart_5241322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241325 : List Nat := [1, 5, 1, 3, 1, 2, 1, 9]
def baseStart_5241325 : Nat := 118140960795 + 5241325 * 2 ^ 59
def prefixEnd_5241325 : Nat := 4983230072969 + 3 ^ 40 * 5241325 * 2
def baseEnd_5241325 : Nat := 99678481163955963908633

theorem tailTrace_5241325 : CollatzResearch.WordTrace tailWord_5241325 prefixEnd_5241325 99678481163955963908633 := by
  unfold tailWord_5241325
  simp only [CollatzResearch.WordTrace]
  refine ⟨191166827736582146888813429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127444551824388097925875619 191166827736582146888813429)
  ·
    refine ⟨17921890100304576270826259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191166827736582146888813429 17921890100304576270826259)
    ·
      refine ⟨26882835150456864406239389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17921890100304576270826259 26882835150456864406239389)
      ·
        refine ⟨10081063181421324152339771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26882835150456864406239389 10081063181421324152339771)
        ·
          refine ⟨15121594772131986228509657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10081063181421324152339771 15121594772131986228509657)
          ·
            refine ⟨11341196079098989671382243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15121594772131986228509657 11341196079098989671382243)
            ·
              refine ⟨17011794118648484507073365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11341196079098989671382243 17011794118648484507073365)
              ·
                refine ⟨99678481163955963908633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17011794118648484507073365 99678481163955963908633)
                ·
                  rfl

theorem cell23_5241325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 9].length) (baseStart_5241325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241325 prefixEnd_5241325 := by exact prefixLift 5241325
  have htrace : WordTrace (prefixWord ++ tailWord_5241325) baseStart_5241325 baseEnd_5241325 := by
    simpa [prefixWord, tailWord_5241325, baseEnd_5241325] using wordTrace_append hprefix tailTrace_5241325
  have hstable : (prefixWord ++ tailWord_5241325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241325).length < 2 ^ (prefixWord ++ tailWord_5241325).sum := by decide
  have hdescent : baseEnd_5241325 < baseStart_5241325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241352 : List Nat := [2, 1, 3, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_5241352 : Nat := 118140960795 + 5241352 * 2 ^ 59
def prefixEnd_5241352 : Nat := 4983230072969 + 3 ^ 40 * 5241352 * 2
def baseEnd_5241352 : Nat := 2691332855404482419895467

theorem tailTrace_5241352 : CollatzResearch.WordTrace tailWord_5241352 prefixEnd_5241352 2691332855404482419895467 := by
  unfold tailWord_5241352
  simp only [CollatzResearch.WordTrace]
  refine ⟨95583906253742165250023155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127445208338322887000030873 95583906253742165250023155)
  ·
    refine ⟨143375859380613247875034733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95583906253742165250023155 143375859380613247875034733)
    ·
      refine ⟨53765947267729967953138025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143375859380613247875034733 53765947267729967953138025)
      ·
        refine ⟨40324460450797475964853519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53765947267729967953138025 40324460450797475964853519)
        ·
          refine ⟨60486690676196213947280279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40324460450797475964853519 60486690676196213947280279)
          ·
            refine ⟨90730036014294320920920419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60486690676196213947280279 90730036014294320920920419)
            ·
              refine ⟨136095054021441481381380629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90730036014294320920920419 136095054021441481381380629)
              ·
                refine ⟨6379455657255069439752217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136095054021441481381380629 6379455657255069439752217)
                ·
                  refine ⟨4784591742941302079814163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6379455657255069439752217 4784591742941302079814163)
                  ·
                    refine ⟨7176887614411953119721245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4784591742941302079814163 7176887614411953119721245)
                    ·
                      refine ⟨2691332855404482419895467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7176887614411953119721245 2691332855404482419895467)
                      ·
                        rfl

theorem cell23_5241352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_5241352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241352 prefixEnd_5241352 := by exact prefixLift 5241352
  have htrace : WordTrace (prefixWord ++ tailWord_5241352) baseStart_5241352 baseEnd_5241352 := by
    simpa [prefixWord, tailWord_5241352, baseEnd_5241352] using wordTrace_append hprefix tailTrace_5241352
  have hstable : (prefixWord ++ tailWord_5241352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241352).length < 2 ^ (prefixWord ++ tailWord_5241352).sum := by decide
  have hdescent : baseEnd_5241352 < baseStart_5241352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241379 : List Nat := [1, 1, 1, 4, 4, 1, 3, 2, 1, 3, 2]
def baseStart_5241379 : Nat := 118140960795 + 5241379 * 2 ^ 59
def prefixEnd_5241379 : Nat := 4983230072969 + 3 ^ 40 * 5241379 * 2
def baseEnd_5241379 : Nat := 2691346719382153814257843

theorem tailTrace_5241379 : CollatzResearch.WordTrace tailWord_5241379 prefixEnd_5241379 2691346719382153814257843 := by
  unfold tailWord_5241379
  simp only [CollatzResearch.WordTrace]
  refine ⟨191168797278386514111279191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127445864852257676074186127 191168797278386514111279191)
  ·
    refine ⟨286753195917579771166918787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191168797278386514111279191 286753195917579771166918787)
    ·
      refine ⟨430129793876369656750378181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286753195917579771166918787 430129793876369656750378181)
      ·
        refine ⟨80649336351819310640695909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 430129793876369656750378181 80649336351819310640695909)
        ·
          refine ⟨15121750565966120745130483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80649336351819310640695909 15121750565966120745130483)
          ·
            refine ⟨22682625848949181117695725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15121750565966120745130483 22682625848949181117695725)
            ·
              refine ⟨8505984693355942919135897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22682625848949181117695725 8505984693355942919135897)
              ·
                refine ⟨6379488520016957189351923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8505984693355942919135897 6379488520016957189351923)
                ·
                  refine ⟨9569232780025435784027885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6379488520016957189351923 9569232780025435784027885)
                  ·
                    refine ⟨3588462292509538419010457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9569232780025435784027885 3588462292509538419010457)
                    ·
                      refine ⟨2691346719382153814257843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588462292509538419010457 2691346719382153814257843)
                      ·
                        rfl

theorem cell23_5241379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_5241379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241379 prefixEnd_5241379 := by exact prefixLift 5241379
  have htrace : WordTrace (prefixWord ++ tailWord_5241379) baseStart_5241379 baseEnd_5241379 := by
    simpa [prefixWord, tailWord_5241379, baseEnd_5241379] using wordTrace_append hprefix tailTrace_5241379
  have hstable : (prefixWord ++ tailWord_5241379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241379).length < 2 ^ (prefixWord ++ tailWord_5241379).sum := by decide
  have hdescent : baseEnd_5241379 < baseStart_5241379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241392 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 6, 2, 2]
def baseStart_5241392 : Nat := 118140960795 + 5241392 * 2 ^ 59
def prefixEnd_5241392 : Nat := 4983230072969 + 3 ^ 40 * 5241392 * 2
def baseEnd_5241392 : Nat := 2691353394630662263395283

theorem tailTrace_5241392 : CollatzResearch.WordTrace tailWord_5241392 prefixEnd_5241392 2691353394630662263395283 := by
  unfold tailWord_5241392
  simp only [CollatzResearch.WordTrace]
  refine ⟨95584635713669708665751215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127446180951559611554334953 95584635713669708665751215)
  ·
    refine ⟨143376953570504562998626823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95584635713669708665751215 143376953570504562998626823)
    ·
      refine ⟨215065430355756844497940235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143376953570504562998626823 215065430355756844497940235)
      ·
        refine ⟨322598145533635266746910353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215065430355756844497940235 322598145533635266746910353)
        ·
          refine ⟨241948609150226450060182765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322598145533635266746910353 241948609150226450060182765)
          ·
            refine ⟨90730728431334918772568537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241948609150226450060182765 90730728431334918772568537)
            ·
              refine ⟨68048046323501189079426403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90730728431334918772568537 68048046323501189079426403)
              ·
                refine ⟨102072069485251783619139605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68048046323501189079426403 102072069485251783619139605)
                ·
                  refine ⟨4784628257121177357147169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102072069485251783619139605 4784628257121177357147169)
                  ·
                    refine ⟨3588471192840883017860377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4784628257121177357147169 3588471192840883017860377)
                    ·
                      refine ⟨2691353394630662263395283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588471192840883017860377 2691353394630662263395283)
                      ·
                        rfl

theorem cell23_5241392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6, 2, 2].length) (baseStart_5241392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241392 prefixEnd_5241392 := by exact prefixLift 5241392
  have htrace : WordTrace (prefixWord ++ tailWord_5241392) baseStart_5241392 baseEnd_5241392 := by
    simpa [prefixWord, tailWord_5241392, baseEnd_5241392] using wordTrace_append hprefix tailTrace_5241392
  have hstable : (prefixWord ++ tailWord_5241392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241392).length < 2 ^ (prefixWord ++ tailWord_5241392).sum := by decide
  have hdescent : baseEnd_5241392 < baseStart_5241392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241408 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 7]
def baseStart_5241408 : Nat := 118140960795 + 5241408 * 2 ^ 59
def prefixEnd_5241408 : Nat := 4983230072969 + 3 ^ 40 * 5241408 * 2
def baseEnd_5241408 : Nat := 2691361610321134200795209

theorem tailTrace_5241408 : CollatzResearch.WordTrace tailWord_5241408 prefixEnd_5241408 2691361610321134200795209 := by
  unfold tailWord_5241408
  simp only [CollatzResearch.WordTrace]
  refine ⟨95584927497640726032042439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127446569996854301376056585 95584927497640726032042439)
  ·
    refine ⟨143377391246461089048063659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95584927497640726032042439 143377391246461089048063659)
    ·
      refine ⟨215066086869691633572095489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143377391246461089048063659 215066086869691633572095489)
      ·
        refine ⟨161299565152268725179071617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215066086869691633572095489 161299565152268725179071617)
        ·
          refine ⟨120974673864201543884303713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161299565152268725179071617 120974673864201543884303713)
          ·
            refine ⟨90731005398151157913227785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120974673864201543884303713 90731005398151157913227785)
            ·
              refine ⟨68048254048613368434920839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90731005398151157913227785 68048254048613368434920839)
              ·
                refine ⟨102072381072920052652381259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68048254048613368434920839 102072381072920052652381259)
                ·
                  refine ⟨153108571609380078978571889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102072381072920052652381259 153108571609380078978571889)
                  ·
                    refine ⟨114831428707035059233928917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 153108571609380078978571889 114831428707035059233928917)
                    ·
                      refine ⟨2691361610321134200795209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114831428707035059233928917 2691361610321134200795209)
                      ·
                        rfl

theorem cell23_5241408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_5241408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241408 prefixEnd_5241408 := by exact prefixLift 5241408
  have htrace : WordTrace (prefixWord ++ tailWord_5241408) baseStart_5241408 baseEnd_5241408 := by
    simpa [prefixWord, tailWord_5241408, baseEnd_5241408] using wordTrace_append hprefix tailTrace_5241408
  have hstable : (prefixWord ++ tailWord_5241408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241408).length < 2 ^ (prefixWord ++ tailWord_5241408).sum := by decide
  have hdescent : baseEnd_5241408 < baseStart_5241408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241425 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 1, 5, 3]
def baseStart_5241425 : Nat := 118140960795 + 5241425 * 2 ^ 59
def prefixEnd_5241425 : Nat := 4983230072969 + 3 ^ 40 * 5241425 * 2
def baseEnd_5241425 : Nat := 2691370339492260634282631

theorem tailTrace_5241425 : CollatzResearch.WordTrace tailWord_5241425 prefixEnd_5241425 2691370339492260634282631 := by
  unfold tailWord_5241425
  simp only [CollatzResearch.WordTrace]
  refine ⟨191170475036219863967453729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127446983357479909311635819 191170475036219863967453729)
  ·
    refine ⟨143377856277164897975590297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191170475036219863967453729 143377856277164897975590297)
    ·
      refine ⟨107533392207873673481692723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143377856277164897975590297 107533392207873673481692723)
      ·
        refine ⟨161300088311810510222539085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107533392207873673481692723 161300088311810510222539085)
        ·
          refine ⟨60487533116928941333452157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161300088311810510222539085 60487533116928941333452157)
          ·
            refine ⟨22682824918848353000044559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60487533116928941333452157 22682824918848353000044559)
            ·
              refine ⟨34024237378272529500066839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22682824918848353000044559 34024237378272529500066839)
              ·
                refine ⟨51036356067408794250100259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34024237378272529500066839 51036356067408794250100259)
                ·
                  refine ⟨76554534101113191375150389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51036356067408794250100259 76554534101113191375150389)
                  ·
                    refine ⟨7176987571979361691420349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76554534101113191375150389 7176987571979361691420349)
                    ·
                      refine ⟨2691370339492260634282631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7176987571979361691420349 2691370339492260634282631)
                      ·
                        rfl

theorem cell23_5241425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_5241425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241425 prefixEnd_5241425 := by exact prefixLift 5241425
  have htrace : WordTrace (prefixWord ++ tailWord_5241425) baseStart_5241425 baseEnd_5241425 := by
    simpa [prefixWord, tailWord_5241425, baseEnd_5241425] using wordTrace_append hprefix tailTrace_5241425
  have hstable : (prefixWord ++ tailWord_5241425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241425).length < 2 ^ (prefixWord ++ tailWord_5241425).sum := by decide
  have hdescent : baseEnd_5241425 < baseStart_5241425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241495 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_5241495 : Nat := 118140960795 + 5241495 * 2 ^ 59
def prefixEnd_5241495 : Nat := 4983230072969 + 3 ^ 40 * 5241495 * 2
def baseEnd_5241495 : Nat := 2691406283138075360407309

theorem tailTrace_5241495 : CollatzResearch.WordTrace tailWord_5241495 prefixEnd_5241495 2691406283138075360407309 := by
  unfold tailWord_5241495
  simp only [CollatzResearch.WordTrace]
  refine ⟨191173028145966265922501939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127448685430644177281667959 191173028145966265922501939)
  ·
    refine ⟨286759542218949398883752909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191173028145966265922501939 286759542218949398883752909)
    ·
      refine ⟨107534828332106024581407341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286759542218949398883752909 107534828332106024581407341)
      ·
        refine ⟨40325560624539759218027753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107534828332106024581407341 40325560624539759218027753)
        ·
          refine ⟨30244170468404819413520815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40325560624539759218027753 30244170468404819413520815)
          ·
            refine ⟨45366255702607229120281223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30244170468404819413520815 45366255702607229120281223)
            ·
              refine ⟨68049383553910843680421835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45366255702607229120281223 68049383553910843680421835)
              ·
                refine ⟨102074075330866265520632753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68049383553910843680421835 102074075330866265520632753)
                ·
                  refine ⟨76555556498149699140474565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102074075330866265520632753 76555556498149699140474565)
                  ·
                    refine ⟨14354166843403068588838981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76555556498149699140474565 14354166843403068588838981)
                    ·
                      refine ⟨2691406283138075360407309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14354166843403068588838981 2691406283138075360407309)
                      ·
                        rfl

theorem cell23_5241495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_5241495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241495 prefixEnd_5241495 := by exact prefixLift 5241495
  have htrace : WordTrace (prefixWord ++ tailWord_5241495) baseStart_5241495 baseEnd_5241495 := by
    simpa [prefixWord, tailWord_5241495, baseEnd_5241495] using wordTrace_append hprefix tailTrace_5241495
  have hstable : (prefixWord ++ tailWord_5241495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241495).length < 2 ^ (prefixWord ++ tailWord_5241495).sum := by decide
  have hdescent : baseEnd_5241495 < baseStart_5241495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241559 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 2, 3, 2]
def baseStart_5241559 : Nat := 118140960795 + 5241559 * 2 ^ 59
def prefixEnd_5241559 : Nat := 4983230072969 + 3 ^ 40 * 5241559 * 2
def baseEnd_5241559 : Nat := 2691439145899963110007015

theorem tailTrace_5241559 : CollatzResearch.WordTrace tailWord_5241559 prefixEnd_5241559 2691439145899963110007015 := by
  unfold tailWord_5241559
  simp only [CollatzResearch.WordTrace]
  refine ⟨191175362417734404852831731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127450241611822936568554487 191175362417734404852831731)
  ·
    refine ⟨286763043626601607279247597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191175362417734404852831731 286763043626601607279247597)
    ·
      refine ⟨107536141359975602729717849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286763043626601607279247597 107536141359975602729717849)
      ·
        refine ⟨80652106019981702047288387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107536141359975602729717849 80652106019981702047288387)
        ·
          refine ⟨120978159029972553070932581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80652106019981702047288387 120978159029972553070932581)
          ·
            refine ⟨22683404818119853700799859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120978159029972553070932581 22683404818119853700799859)
            ·
              refine ⟨34025107227179780551199789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22683404818119853700799859 34025107227179780551199789)
              ·
                refine ⟨12759415210192417706699921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34025107227179780551199789 12759415210192417706699921)
                ·
                  refine ⟨9569561407644313280024941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12759415210192417706699921 9569561407644313280024941)
                  ·
                    refine ⟨3588585527866617480009353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9569561407644313280024941 3588585527866617480009353)
                    ·
                      refine ⟨2691439145899963110007015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588585527866617480009353 2691439145899963110007015)
                      ·
                        rfl

theorem cell23_5241559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_5241559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241559 prefixEnd_5241559 := by exact prefixLift 5241559
  have htrace : WordTrace (prefixWord ++ tailWord_5241559) baseStart_5241559 baseEnd_5241559 := by
    simpa [prefixWord, tailWord_5241559, baseEnd_5241559] using wordTrace_append hprefix tailTrace_5241559
  have hstable : (prefixWord ++ tailWord_5241559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241559).length < 2 ^ (prefixWord ++ tailWord_5241559).sum := by decide
  have hdescent : baseEnd_5241559 < baseStart_5241559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241583 : List Nat := [1, 1, 2, 1, 5, 2, 4, 2, 1, 1, 3]
def baseStart_5241583 : Nat := 118140960795 + 5241583 * 2 ^ 59
def prefixEnd_5241583 : Nat := 4983230072969 + 3 ^ 40 * 5241583 * 2
def baseEnd_5241583 : Nat := 2691451469435671016106905

theorem tailTrace_5241583 : CollatzResearch.WordTrace tailWord_5241583 prefixEnd_5241583 2691451469435671016106905 := by
  unfold tailWord_5241583
  simp only [CollatzResearch.WordTrace]
  refine ⟨191176237769647456951705403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127450825179764971301136935 191176237769647456951705403)
  ·
    refine ⟨286764356654471185427558105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191176237769647456951705403 286764356654471185427558105)
    ·
      refine ⟨215073267490853389070668579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286764356654471185427558105 215073267490853389070668579)
      ·
        refine ⟨322609901236280083606002869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215073267490853389070668579 322609901236280083606002869)
        ·
          refine ⟨30244678240901257838062769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 322609901236280083606002869 30244678240901257838062769)
          ·
            refine ⟨22683508680675943378547077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30244678240901257838062769 22683508680675943378547077)
            ·
              refine ⟨4253157877626739383477577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22683508680675943378547077 4253157877626739383477577)
              ·
                refine ⟨3189868408220054537608183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4253157877626739383477577 3189868408220054537608183)
                ·
                  refine ⟨4784802612330081806412275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189868408220054537608183 4784802612330081806412275)
                  ·
                    refine ⟨7177203918495122709618413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4784802612330081806412275 7177203918495122709618413)
                    ·
                      refine ⟨2691451469435671016106905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7177203918495122709618413 2691451469435671016106905)
                      ·
                        rfl

theorem cell23_5241583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 1, 1, 3].length) (baseStart_5241583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241583 prefixEnd_5241583 := by exact prefixLift 5241583
  have htrace : WordTrace (prefixWord ++ tailWord_5241583) baseStart_5241583 baseEnd_5241583 := by
    simpa [prefixWord, tailWord_5241583, baseEnd_5241583] using wordTrace_append hprefix tailTrace_5241583
  have hstable : (prefixWord ++ tailWord_5241583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241583).length < 2 ^ (prefixWord ++ tailWord_5241583).sum := by decide
  have hdescent : baseEnd_5241583 < baseStart_5241583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241592 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 5, 2, 3]
def baseStart_5241592 : Nat := 118140960795 + 5241592 * 2 ^ 59
def prefixEnd_5241592 : Nat := 4983230072969 + 3 ^ 40 * 5241592 * 2
def baseEnd_5241592 : Nat := 2691456090761561480894363

theorem tailTrace_5241592 : CollatzResearch.WordTrace tailWord_5241592 prefixEnd_5241592 2691456090761561480894363 := by
  unfold tailWord_5241592
  simp only [CollatzResearch.WordTrace]
  refine ⟨95588283013307425744391515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127451044017743234325855353 95588283013307425744391515)
  ·
    refine ⟨143382424519961138616587273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95588283013307425744391515 143382424519961138616587273)
    ·
      refine ⟨107536818389970853962440455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143382424519961138616587273 107536818389970853962440455)
      ·
        refine ⟨161305227584956280943660683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107536818389970853962440455 161305227584956280943660683)
        ·
          refine ⟨241957841377434421415491025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161305227584956280943660683 241957841377434421415491025)
          ·
            refine ⟨181468381033075816061618269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241957841377434421415491025 181468381033075816061618269)
            ·
              refine ⟨68050642887403431023106851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181468381033075816061618269 68050642887403431023106851)
              ·
                refine ⟨102075964331105146534660277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68050642887403431023106851 102075964331105146534660277)
                ·
                  refine ⟨9569621656041107487624401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102075964331105146534660277 9569621656041107487624401)
                  ·
                    refine ⟨7177216242030830615718301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9569621656041107487624401 7177216242030830615718301)
                    ·
                      refine ⟨2691456090761561480894363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7177216242030830615718301 2691456090761561480894363)
                      ·
                        rfl

theorem cell23_5241592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_5241592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241592 prefixEnd_5241592 := by exact prefixLift 5241592
  have htrace : WordTrace (prefixWord ++ tailWord_5241592) baseStart_5241592 baseEnd_5241592 := by
    simpa [prefixWord, tailWord_5241592, baseEnd_5241592] using wordTrace_append hprefix tailTrace_5241592
  have hstable : (prefixWord ++ tailWord_5241592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241592).length < 2 ^ (prefixWord ++ tailWord_5241592).sum := by decide
  have hdescent : baseEnd_5241592 < baseStart_5241592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241605 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_5241605 : Nat := 118140960795 + 5241605 * 2 ^ 59
def prefixEnd_5241605 : Nat := 4983230072969 + 3 ^ 40 * 5241605 * 2
def baseEnd_5241605 : Nat := 2691462766010069930031803

theorem tailTrace_5241605 : CollatzResearch.WordTrace tailWord_5241605 prefixEnd_5241605 2691462766010069930031803 := by
  unfold tailWord_5241605
  simp only [CollatzResearch.WordTrace]
  refine ⟨191177040175567754709006269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127451360117045169806004179 191177040175567754709006269)
  ·
    refine ⟨71691390065837908015877351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191177040175567754709006269 71691390065837908015877351)
    ·
      refine ⟨107537085098756862023816027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71691390065837908015877351 107537085098756862023816027)
      ·
        refine ⟨161305627648135293035724041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107537085098756862023816027 161305627648135293035724041)
        ·
          refine ⟨120979220736101469776793031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161305627648135293035724041 120979220736101469776793031)
          ·
            refine ⟨181468831104152204665189547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120979220736101469776793031 181468831104152204665189547)
            ·
              refine ⟨272203246656228306997784321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181468831104152204665189547 272203246656228306997784321)
              ·
                refine ⟨204152434992171230248338241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272203246656228306997784321 204152434992171230248338241)
                ·
                  refine ⟨153114326244128422686253681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204152434992171230248338241 153114326244128422686253681)
                  ·
                    refine ⟨114835744683096317014690261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 153114326244128422686253681 114835744683096317014690261)
                    ·
                      refine ⟨2691462766010069930031803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114835744683096317014690261 2691462766010069930031803)
                      ·
                        rfl

theorem cell23_5241605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_5241605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241605 prefixEnd_5241605 := by exact prefixLift 5241605
  have htrace : WordTrace (prefixWord ++ tailWord_5241605) baseStart_5241605 baseEnd_5241605 := by
    simpa [prefixWord, tailWord_5241605, baseEnd_5241605] using wordTrace_append hprefix tailTrace_5241605
  have hstable : (prefixWord ++ tailWord_5241605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241605).length < 2 ^ (prefixWord ++ tailWord_5241605).sum := by decide
  have hdescent : baseEnd_5241605 < baseStart_5241605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241623 : List Nat := [1, 1, 3, 4, 3, 2, 2, 1, 1, 1, 4]
def baseStart_5241623 : Nat := 118140960795 + 5241623 * 2 ^ 59
def prefixEnd_5241623 : Nat := 4983230072969 + 3 ^ 40 * 5241623 * 2
def baseEnd_5241623 : Nat := 2691472008661850859606721

theorem tailTrace_5241623 : CollatzResearch.WordTrace tailWord_5241623 prefixEnd_5241623 2691472008661850859606721 := by
  unfold tailWord_5241623
  simp only [CollatzResearch.WordTrace]
  refine ⟨191177696689502543783161523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127451797793001695855441015 191177696689502543783161523)
  ·
    refine ⟨286766545034253815674742285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191177696689502543783161523 286766545034253815674742285)
    ·
      refine ⟨107537454387845180878028357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286766545034253815674742285 107537454387845180878028357)
      ·
        refine ⟨20163272697720971414630317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107537454387845180878028357 20163272697720971414630317)
        ·
          refine ⟨7561227261645364280486369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20163272697720971414630317 7561227261645364280486369)
          ·
            refine ⟨5670920446234023210364777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7561227261645364280486369 5670920446234023210364777)
            ·
              refine ⟨4253190334675517407773583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5670920446234023210364777 4253190334675517407773583)
              ·
                refine ⟨6379785502013276111660375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4253190334675517407773583 6379785502013276111660375)
                ·
                  refine ⟨9569678253019914167490563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6379785502013276111660375 9569678253019914167490563)
                  ·
                    refine ⟨14354517379529871251235845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9569678253019914167490563 14354517379529871251235845)
                    ·
                      refine ⟨2691472008661850859606721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14354517379529871251235845 2691472008661850859606721)
                      ·
                        rfl

theorem cell23_5241623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_5241623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241623 prefixEnd_5241623 := by exact prefixLift 5241623
  have htrace : WordTrace (prefixWord ++ tailWord_5241623) baseStart_5241623 baseEnd_5241623 := by
    simpa [prefixWord, tailWord_5241623, baseEnd_5241623] using wordTrace_append hprefix tailTrace_5241623
  have hstable : (prefixWord ++ tailWord_5241623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241623).length < 2 ^ (prefixWord ++ tailWord_5241623).sum := by decide
  have hdescent : baseEnd_5241623 < baseStart_5241623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241625 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 1, 9]
def baseStart_5241625 : Nat := 118140960795 + 5241625 * 2 ^ 59
def prefixEnd_5241625 : Nat := 4983230072969 + 3 ^ 40 * 5241625 * 2
def baseEnd_5241625 : Nat := 897157678541053283927237

theorem tailTrace_5241625 : CollatzResearch.WordTrace tailWord_5241625 prefixEnd_5241625 897157678541053283927237 := by
  unfold tailWord_5241625
  simp only [CollatzResearch.WordTrace]
  refine ⟨191177769635495298124734329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127451846423663532083156219 191177769635495298124734329)
  ·
    refine ⟨143383327226621473593550747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191177769635495298124734329 143383327226621473593550747)
    ·
      refine ⟨215074990839932210390326121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143383327226621473593550747 215074990839932210390326121)
      ·
        refine ⟨161306243129949157792744591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215074990839932210390326121 161306243129949157792744591)
        ·
          refine ⟨241959364694923736689116887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161306243129949157792744591 241959364694923736689116887)
          ·
            refine ⟨362939047042385605033675331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241959364694923736689116887 362939047042385605033675331)
            ·
              refine ⟨544408570563578407550512997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362939047042385605033675331 544408570563578407550512997)
              ·
                refine ⟨102076606980670951415721187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544408570563578407550512997 102076606980670951415721187)
                ·
                  refine ⟨153114910471006427123581781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102076606980670951415721187 153114910471006427123581781)
                  ·
                    refine ⟨897157678541053283927237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 153114910471006427123581781 897157678541053283927237)
                    ·
                      rfl

theorem cell23_5241625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_5241625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241625 prefixEnd_5241625 := by exact prefixLift 5241625
  have htrace : WordTrace (prefixWord ++ tailWord_5241625) baseStart_5241625 baseEnd_5241625 := by
    simpa [prefixWord, tailWord_5241625, baseEnd_5241625] using wordTrace_append hprefix tailTrace_5241625
  have hstable : (prefixWord ++ tailWord_5241625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241625).length < 2 ^ (prefixWord ++ tailWord_5241625).sum := by decide
  have hdescent : baseEnd_5241625 < baseStart_5241625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241629 : List Nat := [1, 4, 2, 4, 1, 1, 10]
def baseStart_5241629 : Nat := 118140960795 + 5241629 * 2 ^ 59
def prefixEnd_5241629 : Nat := 4983230072969 + 3 ^ 40 * 5241629 * 2
def baseEnd_5241629 : Nat := 33228087525256516495453

theorem tailTrace_5241629 : CollatzResearch.WordTrace tailWord_5241629 prefixEnd_5241629 33228087525256516495453 := by
  unfold tailWord_5241629
  simp only [CollatzResearch.WordTrace]
  refine ⟨191177915527480806807879941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127451943684987204538586627 191177915527480806807879941)
  ·
    refine ⟨35845859161402651276477489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191177915527480806807879941 35845859161402651276477489)
    ·
      refine ⟨26884394371051988457358117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35845859161402651276477489 26884394371051988457358117)
      ·
        refine ⟨5040823944572247835754647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26884394371051988457358117 5040823944572247835754647)
        ·
          refine ⟨7561235916858371753631971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5040823944572247835754647 7561235916858371753631971)
          ·
            refine ⟨11341853875287557630447957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7561235916858371753631971 11341853875287557630447957)
            ·
              refine ⟨33228087525256516495453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11341853875287557630447957 33228087525256516495453)
              ·
                rfl

theorem cell23_5241629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 10].length) (baseStart_5241629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241629 prefixEnd_5241629 := by exact prefixLift 5241629
  have htrace : WordTrace (prefixWord ++ tailWord_5241629) baseStart_5241629 baseEnd_5241629 := by
    simpa [prefixWord, tailWord_5241629, baseEnd_5241629] using wordTrace_append hprefix tailTrace_5241629
  have hstable : (prefixWord ++ tailWord_5241629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241629).length < 2 ^ (prefixWord ++ tailWord_5241629).sum := by decide
  have hdescent : baseEnd_5241629 < baseStart_5241629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241696 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 4, 2, 2]
def baseStart_5241696 : Nat := 118140960795 + 5241696 * 2 ^ 59
def prefixEnd_5241696 : Nat := 4983230072969 + 3 ^ 40 * 5241696 * 2
def baseEnd_5241696 : Nat := 2691509492749629073993885

theorem tailTrace_5241696 : CollatzResearch.WordTrace tailWord_5241696 prefixEnd_5241696 2691509492749629073993885 := by
  unfold tailWord_5241696
  simp only [CollatzResearch.WordTrace]
  refine ⟨95590179609119038625284471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127453572812158718167045961 95590179609119038625284471)
  ·
    refine ⟨143385269413678557937926707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95590179609119038625284471 143385269413678557937926707)
    ·
      refine ⟨215077904120517836906890061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143385269413678557937926707 215077904120517836906890061)
      ·
        refine ⟨80654214045194188840083773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215077904120517836906890061 80654214045194188840083773)
        ·
          refine ⟨30245330266947820815031415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80654214045194188840083773 30245330266947820815031415)
          ·
            refine ⟨45367995400421731222547123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30245330266947820815031415 45367995400421731222547123)
            ·
              refine ⟨68051993100632596833820685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45367995400421731222547123 68051993100632596833820685)
              ·
                refine ⟨25519497412737223812682757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68051993100632596833820685 25519497412737223812682757)
                ·
                  refine ⟨4784905764888229464878017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25519497412737223812682757 4784905764888229464878017)
                  ·
                    refine ⟨3588679323666172098658513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4784905764888229464878017 3588679323666172098658513)
                    ·
                      refine ⟨2691509492749629073993885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588679323666172098658513 2691509492749629073993885)
                      ·
                        rfl

theorem cell23_5241696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_5241696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241696 prefixEnd_5241696 := by exact prefixLift 5241696
  have htrace : WordTrace (prefixWord ++ tailWord_5241696) baseStart_5241696 baseEnd_5241696 := by
    simpa [prefixWord, tailWord_5241696, baseEnd_5241696] using wordTrace_append hprefix tailTrace_5241696
  have hstable : (prefixWord ++ tailWord_5241696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241696).length < 2 ^ (prefixWord ++ tailWord_5241696).sum := by decide
  have hdescent : baseEnd_5241696 < baseStart_5241696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241713 : List Nat := [1, 2, 2, 2, 1, 5, 1, 3, 2, 2, 2]
def baseStart_5241713 : Nat := 118140960795 + 5241713 * 2 ^ 59
def prefixEnd_5241713 : Nat := 4983230072969 + 3 ^ 40 * 5241713 * 2
def baseEnd_5241713 : Nat := 2691518221920755507481307

theorem tailTrace_5241713 : CollatzResearch.WordTrace tailWord_5241713 prefixEnd_5241713 2691518221920755507481307 := by
  unfold tailWord_5241713
  simp only [CollatzResearch.WordTrace]
  refine ⟨191180979259176489153937793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127453986172784326102625195 191180979259176489153937793)
  ·
    refine ⟨143385734444382366865453345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191180979259176489153937793 143385734444382366865453345)
    ·
      refine ⟨107539300833286775149090009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143385734444382366865453345 107539300833286775149090009)
      ·
        refine ⟨80654475624965081361817507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107539300833286775149090009 80654475624965081361817507)
        ·
          refine ⟨120981713437447622042726261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80654475624965081361817507 120981713437447622042726261)
          ·
            refine ⟨11342035634760714566505587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120981713437447622042726261 11342035634760714566505587)
            ·
              refine ⟨17013053452141071849758381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11342035634760714566505587 17013053452141071849758381)
              ·
                refine ⟨6379895044552901943659393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17013053452141071849758381 6379895044552901943659393)
                ·
                  refine ⟨4784921283414676457744545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6379895044552901943659393 4784921283414676457744545)
                  ·
                    refine ⟨3588690962561007343308409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4784921283414676457744545 3588690962561007343308409)
                    ·
                      refine ⟨2691518221920755507481307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588690962561007343308409 2691518221920755507481307)
                      ·
                        rfl

theorem cell23_5241713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_5241713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241713 prefixEnd_5241713 := by exact prefixLift 5241713
  have htrace : WordTrace (prefixWord ++ tailWord_5241713) baseStart_5241713 baseEnd_5241713 := by
    simpa [prefixWord, tailWord_5241713, baseEnd_5241713] using wordTrace_append hprefix tailTrace_5241713
  have hstable : (prefixWord ++ tailWord_5241713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241713).length < 2 ^ (prefixWord ++ tailWord_5241713).sum := by decide
  have hdescent : baseEnd_5241713 < baseStart_5241713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241749 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 2, 5]
def baseStart_5241749 : Nat := 118140960795 + 5241749 * 2 ^ 59
def prefixEnd_5241749 : Nat := 4983230072969 + 3 ^ 40 * 5241749 * 2
def baseEnd_5241749 : Nat := 897178902408105788877047

theorem tailTrace_5241749 : CollatzResearch.WordTrace tailWord_5241749 prefixEnd_5241749 897178902408105788877047 := by
  unfold tailWord_5241749
  simp only [CollatzResearch.WordTrace]
  refine ⟨191182292287046067302248301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127454861524697378201498867 191182292287046067302248301)
  ·
    refine ⟨71693359607642275238343113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191182292287046067302248301 71693359607642275238343113)
    ·
      refine ⟨53770019705731706428757335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71693359607642275238343113 53770019705731706428757335)
      ·
        refine ⟨80655029558597559643136003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53770019705731706428757335 80655029558597559643136003)
        ·
          refine ⟨120982544337896339464704005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80655029558597559643136003 120982544337896339464704005)
          ·
            refine ⟨22684227063355563649632001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120982544337896339464704005 22684227063355563649632001)
            ·
              refine ⟨17013170297516672737224001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22684227063355563649632001 17013170297516672737224001)
              ·
                refine ⟨12759877723137504552918001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17013170297516672737224001 12759877723137504552918001)
                ·
                  refine ⟨9569908292353128414688501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12759877723137504552918001 9569908292353128414688501)
                  ·
                    refine ⟨897178902408105788877047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9569908292353128414688501 897178902408105788877047)
                    ·
                      rfl

theorem cell23_5241749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_5241749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241749 prefixEnd_5241749 := by exact prefixLift 5241749
  have htrace : WordTrace (prefixWord ++ tailWord_5241749) baseStart_5241749 baseEnd_5241749 := by
    simpa [prefixWord, tailWord_5241749, baseEnd_5241749] using wordTrace_append hprefix tailTrace_5241749
  have hstable : (prefixWord ++ tailWord_5241749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241749).length < 2 ^ (prefixWord ++ tailWord_5241749).sum := by decide
  have hdescent : baseEnd_5241749 < baseStart_5241749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241759 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 5]
def baseStart_5241759 : Nat := 118140960795 + 5241759 * 2 ^ 59
def prefixEnd_5241759 : Nat := 4983230072969 + 3 ^ 40 * 5241759 * 2
def baseEnd_5241759 : Nat := 2691541842030862327506095

theorem tailTrace_5241759 : CollatzResearch.WordTrace tailWord_5241759 prefixEnd_5241759 2691541842030862327506095 := by
  unfold tailWord_5241759
  simp only [CollatzResearch.WordTrace]
  refine ⟨191182657017009839010112331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127455104678006559340074887 191182657017009839010112331)
  ·
    refine ⟨286773985525514758515168497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191182657017009839010112331 286773985525514758515168497)
    ·
      refine ⟨215080489144136068886376373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286773985525514758515168497 215080489144136068886376373)
      ·
        refine ⟨20163795857262756458097785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215080489144136068886376373 20163795857262756458097785)
        ·
          refine ⟨15122846892947067343573339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20163795857262756458097785 15122846892947067343573339)
          ·
            refine ⟨22684270339420601015360009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15122846892947067343573339 22684270339420601015360009)
            ·
              refine ⟨17013202754565450761520007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22684270339420601015360009 17013202754565450761520007)
              ·
                refine ⟨25519804131848176142280011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17013202754565450761520007 25519804131848176142280011)
                ·
                  refine ⟨38279706197772264213420017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25519804131848176142280011 38279706197772264213420017)
                  ·
                    refine ⟨28709779648329198160065013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38279706197772264213420017 28709779648329198160065013)
                    ·
                      refine ⟨2691541842030862327506095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28709779648329198160065013 2691541842030862327506095)
                      ·
                        rfl

theorem cell23_5241759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_5241759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241759 prefixEnd_5241759 := by exact prefixLift 5241759
  have htrace : WordTrace (prefixWord ++ tailWord_5241759) baseStart_5241759 baseEnd_5241759 := by
    simpa [prefixWord, tailWord_5241759, baseEnd_5241759] using wordTrace_append hprefix tailTrace_5241759
  have hstable : (prefixWord ++ tailWord_5241759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241759).length < 2 ^ (prefixWord ++ tailWord_5241759).sum := by decide
  have hdescent : baseEnd_5241759 < baseStart_5241759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241772 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_5241772 : Nat := 118140960795 + 5241772 * 2 ^ 59
def prefixEnd_5241772 : Nat := 4983230072969 + 3 ^ 40 * 5241772 * 2
def baseEnd_5241772 : Nat := 2691548517279370776643535

theorem tailTrace_5241772 : CollatzResearch.WordTrace tailWord_5241772 prefixEnd_5241772 2691548517279370776643535 := by
  unfold tailWord_5241772
  simp only [CollatzResearch.WordTrace]
  refine ⟨95591565582981371115167785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127455420777308494820223713 95591565582981371115167785)
  ·
    refine ⟨71693674187236028336375839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95591565582981371115167785 71693674187236028336375839)
    ·
      refine ⟨107540511280854042504563759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71693674187236028336375839 107540511280854042504563759)
      ·
        refine ⟨161310766921281063756845639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107540511280854042504563759 161310766921281063756845639)
        ·
          refine ⟨241966150381921595635268459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161310766921281063756845639 241966150381921595635268459)
          ·
            refine ⟨362949225572882393452902689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241966150381921595635268459 362949225572882393452902689)
            ·
              refine ⟨272211919179661795089677017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362949225572882393452902689 272211919179661795089677017)
              ·
                refine ⟨204158939384746346317257763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272211919179661795089677017 204158939384746346317257763)
                ·
                  refine ⟨306238409077119519475886645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204158939384746346317257763 306238409077119519475886645)
                  ·
                    refine ⟨28709850850979954950864373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 306238409077119519475886645 28709850850979954950864373)
                    ·
                      refine ⟨2691548517279370776643535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28709850850979954950864373 2691548517279370776643535)
                      ·
                        rfl

theorem cell23_5241772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_5241772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241772 prefixEnd_5241772 := by exact prefixLift 5241772
  have htrace : WordTrace (prefixWord ++ tailWord_5241772) baseStart_5241772 baseEnd_5241772 := by
    simpa [prefixWord, tailWord_5241772, baseEnd_5241772] using wordTrace_append hprefix tailTrace_5241772
  have hstable : (prefixWord ++ tailWord_5241772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241772).length < 2 ^ (prefixWord ++ tailWord_5241772).sum := by decide
  have hdescent : baseEnd_5241772 < baseStart_5241772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241798 : List Nat := [6, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_5241798 : Nat := 118140960795 + 5241798 * 2 ^ 59
def prefixEnd_5241798 : Nat := 4983230072969 + 3 ^ 40 * 5241798 * 2
def baseEnd_5241798 : Nat := 2691561867776387674918417

theorem tailTrace_5241798 : CollatzResearch.WordTrace tailWord_5241798 prefixEnd_5241798 2691561867776387674918417 := by
  unfold tailWord_5241798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5974502483245892145961939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127456052975912365780521365 5974502483245892145961939)
  ·
    refine ⟨8961753724868838218942909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5974502483245892145961939 8961753724868838218942909)
    ·
      refine ⟨3360657646825814332103591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8961753724868838218942909 3360657646825814332103591)
      ·
        refine ⟨5040986470238721498155387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3360657646825814332103591 5040986470238721498155387)
        ·
          refine ⟨7561479705358082247233081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5040986470238721498155387 7561479705358082247233081)
          ·
            refine ⟨5671109779018561685424811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7561479705358082247233081 5671109779018561685424811)
            ·
              refine ⟨8506664668527842528137217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5671109779018561685424811 8506664668527842528137217)
              ·
                refine ⟨6379998501395881896102913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8506664668527842528137217 6379998501395881896102913)
                ·
                  refine ⟨4784998876046911422077185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6379998501395881896102913 4784998876046911422077185)
                  ·
                    refine ⟨3588749157035183566557889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4784998876046911422077185 3588749157035183566557889)
                    ·
                      refine ⟨2691561867776387674918417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588749157035183566557889 2691561867776387674918417)
                      ·
                        rfl

theorem cell23_5241798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_5241798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241798 prefixEnd_5241798 := by exact prefixLift 5241798
  have htrace : WordTrace (prefixWord ++ tailWord_5241798) baseStart_5241798 baseEnd_5241798 := by
    simpa [prefixWord, tailWord_5241798, baseEnd_5241798] using wordTrace_append hprefix tailTrace_5241798
  have hstable : (prefixWord ++ tailWord_5241798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241798).length < 2 ^ (prefixWord ++ tailWord_5241798).sum := by decide
  have hdescent : baseEnd_5241798 < baseStart_5241798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241813 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 3, 4]
def baseStart_5241813 : Nat := 118140960795 + 5241813 * 2 ^ 59
def prefixEnd_5241813 : Nat := 4983230072969 + 3 ^ 40 * 5241813 * 2
def baseEnd_5241813 : Nat := 897189856662068372076949

theorem tailTrace_5241813 : CollatzResearch.WordTrace tailWord_5241813 prefixEnd_5241813 897189856662068372076949 := by
  unfold tailWord_5241813
  simp only [CollatzResearch.WordTrace]
  refine ⟨191184626558814206232578093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127456417705876137488385395 191184626558814206232578093)
  ·
    refine ⟨71694234959555327337216785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191184626558814206232578093 71694234959555327337216785)
    ·
      refine ⟨53770676219666495502912589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71694234959555327337216785 53770676219666495502912589)
      ·
        refine ⟨20164003582374935813592221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53770676219666495502912589 20164003582374935813592221)
        ·
          refine ⟨7561501343390600930097083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20164003582374935813592221 7561501343390600930097083)
          ·
            refine ⟨11342252015085901395145625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7561501343390600930097083 11342252015085901395145625)
            ·
              refine ⟨8506689011314426046359219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11342252015085901395145625 8506689011314426046359219)
              ·
                refine ⟨12760033516971639069538829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8506689011314426046359219 12760033516971639069538829)
                ·
                  refine ⟨4785012568864364651077061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12760033516971639069538829 4785012568864364651077061)
                  ·
                    refine ⟨897189856662068372076949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4785012568864364651077061 897189856662068372076949)
                    ·
                      rfl

theorem cell23_5241813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_5241813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241813 prefixEnd_5241813 := by exact prefixLift 5241813
  have htrace : WordTrace (prefixWord ++ tailWord_5241813) baseStart_5241813 baseEnd_5241813 := by
    simpa [prefixWord, tailWord_5241813, baseEnd_5241813] using wordTrace_append hprefix tailTrace_5241813
  have hstable : (prefixWord ++ tailWord_5241813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241813).length < 2 ^ (prefixWord ++ tailWord_5241813).sum := by decide
  have hdescent : baseEnd_5241813 < baseStart_5241813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241859 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 4]
def baseStart_5241859 : Nat := 118140960795 + 5241859 * 2 ^ 59
def prefixEnd_5241859 : Nat := 4983230072969 + 3 ^ 40 * 5241859 * 2
def baseEnd_5241859 : Nat := 2691593190096311936255635

theorem tailTrace_5241859 : CollatzResearch.WordTrace tailWord_5241859 prefixEnd_5241859 2691593190096311936255635 := by
  unfold tailWord_5241859
  simp only [CollatzResearch.WordTrace]
  refine ⟨191186304316647556088752631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127457536211098370725835087 191186304316647556088752631)
  ·
    refine ⟨286779456474971334133128947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191186304316647556088752631 286779456474971334133128947)
    ·
      refine ⟨430169184712457001199693421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286779456474971334133128947 430169184712457001199693421)
      ·
        refine ⟨161313444267171375449885033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430169184712457001199693421 161313444267171375449885033)
        ·
          refine ⟨120985083200378531587413775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161313444267171375449885033 120985083200378531587413775)
          ·
            refine ⟨181477624800567797381120663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120985083200378531587413775 181477624800567797381120663)
            ·
              refine ⟨272216437200851696071680995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181477624800567797381120663 272216437200851696071680995)
              ·
                refine ⟨408324655801277544107521493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272216437200851696071680995 408324655801277544107521493)
                ·
                  refine ⟨9570109120342442440020035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 408324655801277544107521493 9570109120342442440020035)
                  ·
                    refine ⟨14355163680513663660030053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9570109120342442440020035 14355163680513663660030053)
                    ·
                      refine ⟨2691593190096311936255635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14355163680513663660030053 2691593190096311936255635)
                      ·
                        rfl

theorem cell23_5241859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_5241859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241859 prefixEnd_5241859 := by exact prefixLift 5241859
  have htrace : WordTrace (prefixWord ++ tailWord_5241859) baseStart_5241859 baseEnd_5241859 := by
    simpa [prefixWord, tailWord_5241859, baseEnd_5241859] using wordTrace_append hprefix tailTrace_5241859
  have hstable : (prefixWord ++ tailWord_5241859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241859).length < 2 ^ (prefixWord ++ tailWord_5241859).sum := by decide
  have hdescent : baseEnd_5241859 < baseStart_5241859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241863 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 2, 3, 2]
def baseStart_5241863 : Nat := 118140960795 + 5241863 * 2 ^ 59
def prefixEnd_5241863 : Nat := 4983230072969 + 3 ^ 40 * 5241863 * 2
def baseEnd_5241863 : Nat := 2691595244018929920605617

theorem tailTrace_5241863 : CollatzResearch.WordTrace tailWord_5241863 prefixEnd_5241863 2691595244018929920605617 := by
  unfold tailWord_5241863
  simp only [CollatzResearch.WordTrace]
  refine ⟨191186450208633064771898243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127457633472422043181265495 191186450208633064771898243)
  ·
    refine ⟨286779675312949597157847365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191186450208633064771898243 286779675312949597157847365)
    ·
      refine ⟨53771189121178049467096381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286779675312949597157847365 53771189121178049467096381)
      ·
        refine ⟨20164195920441768550161143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53771189121178049467096381 20164195920441768550161143)
        ·
          refine ⟨30246293880662652825241715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20164195920441768550161143 30246293880662652825241715)
          ·
            refine ⟨45369440820993979237862573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30246293880662652825241715 45369440820993979237862573)
            ·
              refine ⟨17013540307872742214198465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45369440820993979237862573 17013540307872742214198465)
              ·
                refine ⟨12760155230904556660648849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17013540307872742214198465 12760155230904556660648849)
                ·
                  refine ⟨9570116423178417495486637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12760155230904556660648849 9570116423178417495486637)
                  ·
                    refine ⟨3588793658691906560807489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9570116423178417495486637 3588793658691906560807489)
                    ·
                      refine ⟨2691595244018929920605617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588793658691906560807489 2691595244018929920605617)
                      ·
                        rfl

theorem cell23_5241863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_5241863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241863 prefixEnd_5241863 := by exact prefixLift 5241863
  have htrace : WordTrace (prefixWord ++ tailWord_5241863) baseStart_5241863 baseEnd_5241863 := by
    simpa [prefixWord, tailWord_5241863, baseEnd_5241863] using wordTrace_append hprefix tailTrace_5241863
  have hstable : (prefixWord ++ tailWord_5241863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241863).length < 2 ^ (prefixWord ++ tailWord_5241863).sum := by decide
  have hdescent : baseEnd_5241863 < baseStart_5241863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241870 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_5241870 : Nat := 118140960795 + 5241870 * 2 ^ 59
def prefixEnd_5241870 : Nat := 4983230072969 + 3 ^ 40 * 5241870 * 2
def baseEnd_5241870 : Nat := 2691598838383511393218085

theorem tailTrace_5241870 : CollatzResearch.WordTrace tailWord_5241870 prefixEnd_5241870 2691598838383511393218085 := by
  unfold tailWord_5241870
  simp only [CollatzResearch.WordTrace]
  refine ⟨23898338189950963120925383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127457803679738469978268709 23898338189950963120925383)
  ·
    refine ⟨35847507284926444681388075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23898338189950963120925383 35847507284926444681388075)
    ·
      refine ⟨53771260927389667022082113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35847507284926444681388075 53771260927389667022082113)
      ·
        refine ⟨40328445695542250266561585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53771260927389667022082113 40328445695542250266561585)
        ·
          refine ⟨30246334271656687699921189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40328445695542250266561585 30246334271656687699921189)
          ·
            refine ⟨5671187675935628943735223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30246334271656687699921189 5671187675935628943735223)
            ·
              refine ⟨8506781513903443415602835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5671187675935628943735223 8506781513903443415602835)
              ·
                refine ⟨12760172270855165123404253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8506781513903443415602835 12760172270855165123404253)
                ·
                  refine ⟨4785064601570686921276595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12760172270855165123404253 4785064601570686921276595)
                  ·
                    refine ⟨7177596902356030381914893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4785064601570686921276595 7177596902356030381914893)
                    ·
                      refine ⟨2691598838383511393218085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7177596902356030381914893 2691598838383511393218085)
                      ·
                        rfl

theorem cell23_5241870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_5241870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241870 prefixEnd_5241870 := by exact prefixLift 5241870
  have htrace : WordTrace (prefixWord ++ tailWord_5241870) baseStart_5241870 baseEnd_5241870 := by
    simpa [prefixWord, tailWord_5241870, baseEnd_5241870] using wordTrace_append hprefix tailTrace_5241870
  have hstable : (prefixWord ++ tailWord_5241870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241870).length < 2 ^ (prefixWord ++ tailWord_5241870).sum := by decide
  have hdescent : baseEnd_5241870 < baseStart_5241870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241893 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 5, 2, 2]
def baseStart_5241893 : Nat := 118140960795 + 5241893 * 2 ^ 59
def prefixEnd_5241893 : Nat := 4983230072969 + 3 ^ 40 * 5241893 * 2
def baseEnd_5241893 : Nat := 2691610648438564803230479

theorem tailTrace_5241893 : CollatzResearch.WordTrace tailWord_5241893 prefixEnd_5241893 2691610648438564803230479 := by
  unfold tailWord_5241893
  simp only [CollatzResearch.WordTrace]
  refine ⟨191187544398524379895490333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127458362932349586596993555 191187544398524379895490333)
  ·
    refine ⟨71695329149446642460808875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191187544398524379895490333 71695329149446642460808875)
    ·
      refine ⟨107542993724169963691213313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71695329149446642460808875 107542993724169963691213313)
      ·
        refine ⟨80657245293127472768409985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107542993724169963691213313 80657245293127472768409985)
        ·
          refine ⟨60492933969845604576307489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80657245293127472768409985 60492933969845604576307489)
          ·
            refine ⟨45369700477384203432230617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60492933969845604576307489 45369700477384203432230617)
            ·
              refine ⟨34027275358038152574172963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45369700477384203432230617 34027275358038152574172963)
              ·
                refine ⟨51040913037057228861259445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34027275358038152574172963 51040913037057228861259445)
                ·
                  refine ⟨4785085597224115205743073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51040913037057228861259445 4785085597224115205743073)
                  ·
                    refine ⟨3588814197918086404307305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4785085597224115205743073 3588814197918086404307305)
                    ·
                      refine ⟨2691610648438564803230479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588814197918086404307305 2691610648438564803230479)
                      ·
                        rfl

theorem cell23_5241893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_5241893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241893 prefixEnd_5241893 := by exact prefixLift 5241893
  have htrace : WordTrace (prefixWord ++ tailWord_5241893) baseStart_5241893 baseEnd_5241893 := by
    simpa [prefixWord, tailWord_5241893, baseEnd_5241893] using wordTrace_append hprefix tailTrace_5241893
  have hstable : (prefixWord ++ tailWord_5241893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241893).length < 2 ^ (prefixWord ++ tailWord_5241893).sum := by decide
  have hdescent : baseEnd_5241893 < baseStart_5241893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241906 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_5241906 : Nat := 118140960795 + 5241906 * 2 ^ 59
def prefixEnd_5241906 : Nat := 4983230072969 + 3 ^ 40 * 5241906 * 2
def baseEnd_5241906 : Nat := 2691617323687073252367919

theorem tailTrace_5241906 : CollatzResearch.WordTrace tailWord_5241906 prefixEnd_5241906 2691617323687073252367919 := by
  unfold tailWord_5241906
  simp only [CollatzResearch.WordTrace]
  refine ⟨47797004636869320778928393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127458679031651522077142381 47797004636869320778928393)
  ·
    refine ⟨35847753477651990584196295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47797004636869320778928393 35847753477651990584196295)
    ·
      refine ⟨53771630216477985876294443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35847753477651990584196295 53771630216477985876294443)
      ·
        refine ⟨80657445324716978814441665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53771630216477985876294443 80657445324716978814441665)
        ·
          refine ⟨60493083993537734110831249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80657445324716978814441665 60493083993537734110831249)
          ·
            refine ⟨45369812995153300583123437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60493083993537734110831249 45369812995153300583123437)
            ·
              refine ⟨17013679873182487718671289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45369812995153300583123437 17013679873182487718671289)
              ·
                refine ⟨12760259904886865789003467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17013679873182487718671289 12760259904886865789003467)
                ·
                  refine ⟨19140389857330298683505201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12760259904886865789003467 19140389857330298683505201)
                  ·
                    refine ⟨14355292392997724012628901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19140389857330298683505201 14355292392997724012628901)
                    ·
                      refine ⟨2691617323687073252367919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14355292392997724012628901 2691617323687073252367919)
                      ·
                        rfl

theorem cell23_5241906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_5241906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241906 prefixEnd_5241906 := by exact prefixLift 5241906
  have htrace : WordTrace (prefixWord ++ tailWord_5241906) baseStart_5241906 baseEnd_5241906 := by
    simpa [prefixWord, tailWord_5241906, baseEnd_5241906] using wordTrace_append hprefix tailTrace_5241906
  have hstable : (prefixWord ++ tailWord_5241906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241906).length < 2 ^ (prefixWord ++ tailWord_5241906).sum := by decide
  have hdescent : baseEnd_5241906 < baseStart_5241906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241913 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 5]
def baseStart_5241913 : Nat := 118140960795 + 5241913 * 2 ^ 59
def prefixEnd_5241913 : Nat := 4983230072969 + 3 ^ 40 * 5241913 * 2
def baseEnd_5241913 : Nat := 2691620918051654724980387

theorem tailTrace_5241913 : CollatzResearch.WordTrace tailWord_5241913 prefixEnd_5241913 2691620918051654724980387 := by
  unfold tailWord_5241913
  simp only [CollatzResearch.WordTrace]
  refine ⟨191188273858451923311218393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127458849238967948874145595 191188273858451923311218393)
  ·
    refine ⟨143391205393838942483413795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191188273858451923311218393 143391205393838942483413795)
    ·
      refine ⟨215086808090758413725120693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143391205393838942483413795 215086808090758413725120693)
      ·
        refine ⟨20164388258508601286730065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215086808090758413725120693 20164388258508601286730065)
        ·
          refine ⟨15123291193881450965047549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20164388258508601286730065 15123291193881450965047549)
          ·
            refine ⟨5671234197705544111892831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15123291193881450965047549 5671234197705544111892831)
            ·
              refine ⟨8506851296558316167839247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5671234197705544111892831 8506851296558316167839247)
              ·
                refine ⟨12760276944837474251758871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8506851296558316167839247 12760276944837474251758871)
                ·
                  refine ⟨19140415417256211377638307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12760276944837474251758871 19140415417256211377638307)
                  ·
                    refine ⟨28710623125884317066457461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19140415417256211377638307 28710623125884317066457461)
                    ·
                      refine ⟨2691620918051654724980387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28710623125884317066457461 2691620918051654724980387)
                      ·
                        rfl

theorem cell23_5241913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_5241913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241913 prefixEnd_5241913 := by exact prefixLift 5241913
  have htrace : WordTrace (prefixWord ++ tailWord_5241913) baseStart_5241913 baseEnd_5241913 := by
    simpa [prefixWord, tailWord_5241913, baseEnd_5241913] using wordTrace_append hprefix tailTrace_5241913
  have hstable : (prefixWord ++ tailWord_5241913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241913).length < 2 ^ (prefixWord ++ tailWord_5241913).sum := by decide
  have hdescent : baseEnd_5241913 < baseStart_5241913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241921 : List Nat := [1, 2, 5, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_5241921 : Nat := 118140960795 + 5241921 * 2 ^ 59
def prefixEnd_5241921 : Nat := 4983230072969 + 3 ^ 40 * 5241921 * 2
def baseEnd_5241921 : Nat := 2691625025896890693680351

theorem tailTrace_5241921 : CollatzResearch.WordTrace tailWord_5241921 prefixEnd_5241921 2691625025896890693680351 := by
  unfold tailWord_5241921
  simp only [CollatzResearch.WordTrace]
  refine ⟨191188565642422940677509617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127459043761615293785006411 191188565642422940677509617)
  ·
    refine ⟨143391424231817205508132213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191188565642422940677509617 143391424231817205508132213)
    ·
      refine ⟨13442946021732863016387395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143391424231817205508132213 13442946021732863016387395)
      ·
        refine ⟨20164419032599294524581093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13442946021732863016387395 20164419032599294524581093)
        ·
          refine ⟨3780828568612367723358955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20164419032599294524581093 3780828568612367723358955)
          ·
            refine ⟨5671242852918551585038433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3780828568612367723358955 5671242852918551585038433)
            ·
              refine ⟨4253432139688913688778825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5671242852918551585038433 4253432139688913688778825)
              ·
                refine ⟨3190074104766685266584119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4253432139688913688778825 3190074104766685266584119)
                ·
                  refine ⟨4785111157150027899876179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3190074104766685266584119 4785111157150027899876179)
                  ·
                    refine ⟨7177666735725041849814269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4785111157150027899876179 7177666735725041849814269)
                    ·
                      refine ⟨2691625025896890693680351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7177666735725041849814269 2691625025896890693680351)
                      ·
                        rfl

theorem cell23_5241921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_5241921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241921 prefixEnd_5241921 := by exact prefixLift 5241921
  have htrace : WordTrace (prefixWord ++ tailWord_5241921) baseStart_5241921 baseEnd_5241921 := by
    simpa [prefixWord, tailWord_5241921, baseEnd_5241921] using wordTrace_append hprefix tailTrace_5241921
  have hstable : (prefixWord ++ tailWord_5241921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241921).length < 2 ^ (prefixWord ++ tailWord_5241921).sum := by decide
  have hdescent : baseEnd_5241921 < baseStart_5241921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241927 : List Nat := [1, 1, 4, 1, 3, 3, 1, 4, 1, 2, 2]
def baseStart_5241927 : Nat := 118140960795 + 5241927 * 2 ^ 59
def prefixEnd_5241927 : Nat := 4983230072969 + 3 ^ 40 * 5241927 * 2
def baseEnd_5241927 : Nat := 2691628106780817670205323

theorem tailTrace_5241927 : CollatzResearch.WordTrace tailWord_5241927 prefixEnd_5241927 2691628106780817670205323 := by
  unfold tailWord_5241927
  simp only [CollatzResearch.WordTrace]
  refine ⟨191188784480401203702228035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127459189653600802468152023 191188784480401203702228035)
  ·
    refine ⟨286783176720601805553342053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191188784480401203702228035 286783176720601805553342053)
    ·
      refine ⟨53771845635112838541251635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286783176720601805553342053 53771845635112838541251635)
      ·
        refine ⟨80657768452669257811877453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53771845635112838541251635 80657768452669257811877453)
        ·
          refine ⟨30246663169750971679454045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80657768452669257811877453 30246663169750971679454045)
          ·
            refine ⟨11342498688656614379795267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30246663169750971679454045 11342498688656614379795267)
            ·
              refine ⟨17013748032984921569692901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11342498688656614379795267 17013748032984921569692901)
              ·
                refine ⟨3190077756184672794317419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17013748032984921569692901 3190077756184672794317419)
                ·
                  refine ⟨4785116634277009191476129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3190077756184672794317419 4785116634277009191476129)
                  ·
                    refine ⟨3588837475707756893607097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4785116634277009191476129 3588837475707756893607097)
                    ·
                      refine ⟨2691628106780817670205323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588837475707756893607097 2691628106780817670205323)
                      ·
                        rfl

theorem cell23_5241927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_5241927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241927 prefixEnd_5241927 := by exact prefixLift 5241927
  have htrace : WordTrace (prefixWord ++ tailWord_5241927) baseStart_5241927 baseEnd_5241927 := by
    simpa [prefixWord, tailWord_5241927, baseEnd_5241927] using wordTrace_append hprefix tailTrace_5241927
  have hstable : (prefixWord ++ tailWord_5241927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241927).length < 2 ^ (prefixWord ++ tailWord_5241927).sum := by decide
  have hdescent : baseEnd_5241927 < baseStart_5241927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241933 : List Nat := [1, 6, 1, 1, 1, 4, 1, 8]
def baseStart_5241933 : Nat := 118140960795 + 5241933 * 2 ^ 59
def prefixEnd_5241933 : Nat := 4983230072969 + 3 ^ 40 * 5241933 * 2
def baseEnd_5241933 : Nat := 99690043987583135064085

theorem tailTrace_5241933 : CollatzResearch.WordTrace tailWord_5241933 prefixEnd_5241933 99690043987583135064085 := by
  unfold tailWord_5241933
  simp only [CollatzResearch.WordTrace]
  refine ⟨191189003318379466726946453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127459335545586311151297635 191189003318379466726946453)
  ·
    refine ⟨8961984530549037502825615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 191189003318379466726946453 8961984530549037502825615)
    ·
      refine ⟨13442976795823556254238423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8961984530549037502825615 13442976795823556254238423)
      ·
        refine ⟨20164465193735334381357635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13442976795823556254238423 20164465193735334381357635)
        ·
          refine ⟨30246697790603001572036453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20164465193735334381357635 30246697790603001572036453)
          ·
            refine ⟨5671255835738062794756835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30246697790603001572036453 5671255835738062794756835)
            ·
              refine ⟨8506883753607094192135253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5671255835738062794756835 8506883753607094192135253)
              ·
                refine ⟨99690043987583135064085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8506883753607094192135253 99690043987583135064085)
                ·
                  rfl

theorem cell23_5241933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 8].length) (baseStart_5241933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241933 prefixEnd_5241933 := by exact prefixLift 5241933
  have htrace : WordTrace (prefixWord ++ tailWord_5241933) baseStart_5241933 baseEnd_5241933 := by
    simpa [prefixWord, tailWord_5241933, baseEnd_5241933] using wordTrace_append hprefix tailTrace_5241933
  have hstable : (prefixWord ++ tailWord_5241933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241933).length < 2 ^ (prefixWord ++ tailWord_5241933).sum := by decide
  have hdescent : baseEnd_5241933 < baseStart_5241933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241953 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 3, 3, 2]
def baseStart_5241953 : Nat := 118140960795 + 5241953 * 2 ^ 59
def prefixEnd_5241953 : Nat := 4983230072969 + 3 ^ 40 * 5241953 * 2
def baseEnd_5241953 : Nat := 2691641457277834568480203

theorem tailTrace_5241953 : CollatzResearch.WordTrace tailWord_5241953 prefixEnd_5241953 2691641457277834568480203 := by
  unfold tailWord_5241953
  simp only [CollatzResearch.WordTrace]
  refine ⟨191189732778307010142674513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127459821852204673428449675 191189732778307010142674513)
  ·
    refine ⟨143392299583730257607005885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191189732778307010142674513 143392299583730257607005885)
    ·
      refine ⟨53772112343898846602627207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143392299583730257607005885 53772112343898846602627207)
      ·
        refine ⟨80658168515848269903940811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53772112343898846602627207 80658168515848269903940811)
        ·
          refine ⟨120987252773772404855911217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80658168515848269903940811 120987252773772404855911217)
          ·
            refine ⟨90740439580329303641933413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120987252773772404855911217 90740439580329303641933413)
            ·
              refine ⟨17013832421311744432862515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90740439580329303641933413 17013832421311744432862515)
              ·
                refine ⟨25520748631967616649293773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17013832421311744432862515 25520748631967616649293773)
                ·
                  refine ⟨9570280736987856243485165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25520748631967616649293773 9570280736987856243485165)
                  ·
                    refine ⟨3588855276370446091306937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9570280736987856243485165 3588855276370446091306937)
                    ·
                      refine ⟨2691641457277834568480203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588855276370446091306937 2691641457277834568480203)
                      ·
                        rfl

theorem cell23_5241953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_5241953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241953 prefixEnd_5241953 := by exact prefixLift 5241953
  have htrace : WordTrace (prefixWord ++ tailWord_5241953) baseStart_5241953 baseEnd_5241953 := by
    simpa [prefixWord, tailWord_5241953, baseEnd_5241953] using wordTrace_append hprefix tailTrace_5241953
  have hstable : (prefixWord ++ tailWord_5241953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241953).length < 2 ^ (prefixWord ++ tailWord_5241953).sum := by decide
  have hdescent : baseEnd_5241953 < baseStart_5241953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241970 : List Nat := [3, 2, 1, 2, 2, 1, 3, 3, 1, 3, 2]
def baseStart_5241970 : Nat := 118140960795 + 5241970 * 2 ^ 59
def prefixEnd_5241970 : Nat := 4983230072969 + 3 ^ 40 * 5241970 * 2
def baseEnd_5241970 : Nat := 2691650186448961001967625

theorem tailTrace_5241970 : CollatzResearch.WordTrace tailWord_5241970 prefixEnd_5241970 2691650186448961001967625 := by
  unfold tailWord_5241970
  simp only [CollatzResearch.WordTrace]
  refine ⟨47797588204811355511510841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127460235212830281364028909 47797588204811355511510841)
  ·
    refine ⟨35848191153608516633633131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47797588204811355511510841 35848191153608516633633131)
    ·
      refine ⟨53772286730412774950449697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35848191153608516633633131 53772286730412774950449697)
      ·
        refine ⟨40329215047809581212837273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53772286730412774950449697 40329215047809581212837273)
        ·
          refine ⟨30246911285857185909627955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40329215047809581212837273 30246911285857185909627955)
          ·
            refine ⟨45370366928785778864441933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30246911285857185909627955 45370366928785778864441933)
            ·
              refine ⟨17013887598294667074165725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45370366928785778864441933 17013887598294667074165725)
              ·
                refine ⟨6380207849360500152812147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17013887598294667074165725 6380207849360500152812147)
                ·
                  refine ⟨9570311774040750229218221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6380207849360500152812147 9570311774040750229218221)
                  ·
                    refine ⟨3588866915265281335956833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9570311774040750229218221 3588866915265281335956833)
                    ·
                      refine ⟨2691650186448961001967625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588866915265281335956833 2691650186448961001967625)
                      ·
                        rfl

theorem cell23_5241970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_5241970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241970 prefixEnd_5241970 := by exact prefixLift 5241970
  have htrace : WordTrace (prefixWord ++ tailWord_5241970) baseStart_5241970 baseEnd_5241970 := by
    simpa [prefixWord, tailWord_5241970, baseEnd_5241970] using wordTrace_append hprefix tailTrace_5241970
  have hstable : (prefixWord ++ tailWord_5241970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241970).length < 2 ^ (prefixWord ++ tailWord_5241970).sum := by decide
  have hdescent : baseEnd_5241970 < baseStart_5241970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5241977 : List Nat := [1, 2, 1, 3, 5, 2, 1, 2, 2, 1, 3]
def baseStart_5241977 : Nat := 118140960795 + 5241977 * 2 ^ 59
def prefixEnd_5241977 : Nat := 4983230072969 + 3 ^ 40 * 5241977 * 2
def baseEnd_5241977 : Nat := 2691653780813542474580093

theorem tailTrace_5241977 : CollatzResearch.WordTrace tailWord_5241977 prefixEnd_5241977 2691653780813542474580093 := by
  unfold tailWord_5241977
  simp only [CollatzResearch.WordTrace]
  refine ⟨191190608130220062241548185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127460405420146708161032123 191190608130220062241548185)
  ·
    refine ⟨143392956097665046681161139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191190608130220062241548185 143392956097665046681161139)
    ·
      refine ⟨215089434146497570021741709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143392956097665046681161139 215089434146497570021741709)
      ·
        refine ⟨80658537804936588758153141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215089434146497570021741709 80658537804936588758153141)
        ·
          refine ⟨7561737919212805196076857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80658537804936588758153141 7561737919212805196076857)
          ·
            refine ⟨5671303439409603897057643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7561737919212805196076857 5671303439409603897057643)
            ·
              refine ⟨8506955159114405845586465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5671303439409603897057643 8506955159114405845586465)
              ·
                refine ⟨6380216369335804384189849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8506955159114405845586465 6380216369335804384189849)
                ·
                  refine ⟨4785162277001853288142387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6380216369335804384189849 4785162277001853288142387)
                  ·
                    refine ⟨7177743415502779932213581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4785162277001853288142387 7177743415502779932213581)
                    ·
                      refine ⟨2691653780813542474580093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7177743415502779932213581 2691653780813542474580093)
                      ·
                        rfl

theorem cell23_5241977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_5241977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5241977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5241977 prefixEnd_5241977 := by exact prefixLift 5241977
  have htrace : WordTrace (prefixWord ++ tailWord_5241977) baseStart_5241977 baseEnd_5241977 := by
    simpa [prefixWord, tailWord_5241977, baseEnd_5241977] using wordTrace_append hprefix tailTrace_5241977
  have hstable : (prefixWord ++ tailWord_5241977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5241977).length < 2 ^ (prefixWord ++ tailWord_5241977).sum := by decide
  have hdescent : baseEnd_5241977 < baseStart_5241977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5241977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242056 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_5242056 : Nat := 118140960795 + 5242056 * 2 ^ 59
def prefixEnd_5242056 : Nat := 4983230072969 + 3 ^ 40 * 5242056 * 2
def baseEnd_5242056 : Nat := 2691694345785247665492229

theorem tailTrace_5242056 : CollatzResearch.WordTrace tailWord_5242056 prefixEnd_5242056 2691694345785247665492229 := by
  unfold tailWord_5242056
  simp only [CollatzResearch.WordTrace]
  refine ⟨95596744748466929366837011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127462326331289239155782681 95596744748466929366837011)
  ·
    refine ⟨143395117122700394050255517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95596744748466929366837011 143395117122700394050255517)
    ·
      refine ⟨53773168921012647768845819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143395117122700394050255517 53773168921012647768845819)
      ·
        refine ⟨80659753381518971653268729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53773168921012647768845819 80659753381518971653268729)
        ·
          refine ⟨60494815036139228739951547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80659753381518971653268729 60494815036139228739951547)
          ·
            refine ⟨90742222554208843109927321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60494815036139228739951547 90742222554208843109927321)
            ·
              refine ⟨68056666915656632332445491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90742222554208843109927321 68056666915656632332445491)
              ·
                refine ⟨102085000373484948498668237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68056666915656632332445491 102085000373484948498668237)
                ·
                  refine ⟨38281875140056855687000589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102085000373484948498668237 38281875140056855687000589)
                  ·
                    refine ⟨14355703177521320882625221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38281875140056855687000589 14355703177521320882625221)
                    ·
                      refine ⟨2691694345785247665492229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14355703177521320882625221 2691694345785247665492229)
                      ·
                        rfl

theorem cell23_5242056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_5242056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242056 prefixEnd_5242056 := by exact prefixLift 5242056
  have htrace : WordTrace (prefixWord ++ tailWord_5242056) baseStart_5242056 baseEnd_5242056 := by
    simpa [prefixWord, tailWord_5242056, baseEnd_5242056] using wordTrace_append hprefix tailTrace_5242056
  have hstable : (prefixWord ++ tailWord_5242056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242056).length < 2 ^ (prefixWord ++ tailWord_5242056).sum := by decide
  have hdescent : baseEnd_5242056 < baseStart_5242056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242073 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 4, 4, 2]
def baseStart_5242073 : Nat := 118140960795 + 5242073 * 2 ^ 59
def prefixEnd_5242073 : Nat := 4983230072969 + 3 ^ 40 * 5242073 * 2
def baseEnd_5242073 : Nat := 2691703074956374098979651

theorem tailTrace_5242073 : CollatzResearch.WordTrace tailWord_5242073 prefixEnd_5242073 2691703074956374098979651 := by
  unfold tailWord_5242073
  simp only [CollatzResearch.WordTrace]
  refine ⟨191194109537872270637042873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127462739691914847091361915 191194109537872270637042873)
  ·
    refine ⟨143395582153404202977782155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191194109537872270637042873 143395582153404202977782155)
    ·
      refine ⟨215093373230106304466673233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143395582153404202977782155 215093373230106304466673233)
      ·
        refine ⟨161320029922579728350004925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215093373230106304466673233 161320029922579728350004925)
        ·
          refine ⟨60495011220967398131251847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161320029922579728350004925 60495011220967398131251847)
          ·
            refine ⟨90742516831451097196877771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60495011220967398131251847 90742516831451097196877771)
            ·
              refine ⟨136113775247176645795316657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90742516831451097196877771 136113775247176645795316657)
              ·
                refine ⟨102085331435382484346487493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136113775247176645795316657 102085331435382484346487493)
                ·
                  refine ⟨19140999644134215814966405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102085331435382484346487493 19140999644134215814966405)
                  ·
                    refine ⟨3588937433275165465306201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19140999644134215814966405 3588937433275165465306201)
                    ·
                      refine ⟨2691703074956374098979651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3588937433275165465306201 2691703074956374098979651)
                      ·
                        rfl

theorem cell23_5242073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 4, 2].length) (baseStart_5242073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242073 prefixEnd_5242073 := by exact prefixLift 5242073
  have htrace : WordTrace (prefixWord ++ tailWord_5242073) baseStart_5242073 baseEnd_5242073 := by
    simpa [prefixWord, tailWord_5242073, baseEnd_5242073] using wordTrace_append hprefix tailTrace_5242073
  have hstable : (prefixWord ++ tailWord_5242073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242073).length < 2 ^ (prefixWord ++ tailWord_5242073).sum := by decide
  have hdescent : baseEnd_5242073 < baseStart_5242073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242113 : List Nat := [1, 2, 4, 1, 1, 3, 2, 3, 6]
def baseStart_5242113 : Nat := 118140960795 + 5242113 * 2 ^ 59
def prefixEnd_5242113 : Nat := 4983230072969 + 3 ^ 40 * 5242113 * 2
def baseEnd_5242113 : Nat := 299080401575839326942163

theorem tailTrace_5242113 : CollatzResearch.WordTrace tailWord_5242113 prefixEnd_5242113 299080401575839326942163 := by
  unfold tailWord_5242113
  simp only [CollatzResearch.WordTrace]
  refine ⟨191195568457727357468498993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127463712305151571645665995 191195568457727357468498993)
  ·
    refine ⟨143396676343295518101374245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191195568457727357468498993 143396676343295518101374245)
    ·
      refine ⟨26886876814367909644007671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143396676343295518101374245 26886876814367909644007671)
      ·
        refine ⟨40330315221551864466011507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26886876814367909644007671 40330315221551864466011507)
        ·
          refine ⟨60495472832327796699017261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40330315221551864466011507 60495472832327796699017261)
          ·
            refine ⟨22685802312122923762131473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60495472832327796699017261 22685802312122923762131473)
            ·
              refine ⟨17014351734092192821598605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22685802312122923762131473 17014351734092192821598605)
              ·
                refine ⟨6380381900284572308099477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17014351734092192821598605 6380381900284572308099477)
                ·
                  refine ⟨299080401575839326942163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6380381900284572308099477 299080401575839326942163)
                  ·
                    rfl

theorem cell23_5242113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 6].length) (baseStart_5242113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242113 prefixEnd_5242113 := by exact prefixLift 5242113
  have htrace : WordTrace (prefixWord ++ tailWord_5242113) baseStart_5242113 baseEnd_5242113 := by
    simpa [prefixWord, tailWord_5242113, baseEnd_5242113] using wordTrace_append hprefix tailTrace_5242113
  have hstable : (prefixWord ++ tailWord_5242113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242113).length < 2 ^ (prefixWord ++ tailWord_5242113).sum := by decide
  have hdescent : baseEnd_5242113 < baseStart_5242113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242177 : List Nat := [1, 2, 5, 2, 1, 2, 2, 2, 1, 5]
def baseStart_5242177 : Nat := 118140960795 + 5242177 * 2 ^ 59
def prefixEnd_5242177 : Nat := 4983230072969 + 3 ^ 40 * 5242177 * 2
def baseEnd_5242177 : Nat := 897252158981480564026391

theorem tailTrace_5242177 : CollatzResearch.WordTrace tailWord_5242177 prefixEnd_5242177 897252158981480564026391 := by
  unfold tailWord_5242177
  simp only [CollatzResearch.WordTrace]
  refine ⟨191197902729495496398828785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127465268486330330932552523 191197902729495496398828785)
  ·
    refine ⟨143398427047121622299121589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191197902729495496398828785 143398427047121622299121589)
    ·
      refine ⟨13443602535667652090542649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143398427047121622299121589 13443602535667652090542649)
      ·
        refine ⟨10082701901750739067906987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13443602535667652090542649 10082701901750739067906987)
        ·
          refine ⟨15124052852626108601860481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10082701901750739067906987 15124052852626108601860481)
          ·
            refine ⟨11343039639469581451395361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15124052852626108601860481 11343039639469581451395361)
            ·
              refine ⟨8507279729602186088546521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11343039639469581451395361 8507279729602186088546521)
              ·
                refine ⟨6380459797201639566409891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8507279729602186088546521 6380459797201639566409891)
                ·
                  refine ⟨9570689695802459349614837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6380459797201639566409891 9570689695802459349614837)
                  ·
                    refine ⟨897252158981480564026391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9570689695802459349614837 897252158981480564026391)
                    ·
                      rfl

theorem cell23_5242177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_5242177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242177 prefixEnd_5242177 := by exact prefixLift 5242177
  have htrace : WordTrace (prefixWord ++ tailWord_5242177) baseStart_5242177 baseEnd_5242177 := by
    simpa [prefixWord, tailWord_5242177, baseEnd_5242177] using wordTrace_append hprefix tailTrace_5242177
  have hstable : (prefixWord ++ tailWord_5242177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242177).length < 2 ^ (prefixWord ++ tailWord_5242177).sum := by decide
  have hdescent : baseEnd_5242177 < baseStart_5242177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242193 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_5242193 : Nat := 118140960795 + 5242193 * 2 ^ 59
def prefixEnd_5242193 : Nat := 4983230072969 + 3 ^ 40 * 5242193 * 2
def baseEnd_5242193 : Nat := 2691764692634913629479099

theorem tailTrace_5242193 : CollatzResearch.WordTrace tailWord_5242193 prefixEnd_5242193 2691764692634913629479099 := by
  unfold tailWord_5242193
  simp only [CollatzResearch.WordTrace]
  refine ⟨191198486297437531131411233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127465657531625020754274155 191198486297437531131411233)
  ·
    refine ⟨143398864723078148348558425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191198486297437531131411233 143398864723078148348558425)
    ·
      refine ⟨107549148542308611261418819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143398864723078148348558425 107549148542308611261418819)
      ·
        refine ⟨161323722813462916892128229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107549148542308611261418819 161323722813462916892128229)
        ·
          refine ⟨30248198027524296917274043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161323722813462916892128229 30248198027524296917274043)
          ·
            refine ⟨45372297041286445375911065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30248198027524296917274043 45372297041286445375911065)
            ·
              refine ⟨34029222780964834031933299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45372297041286445375911065 34029222780964834031933299)
              ·
                refine ⟨51043834171447251047899949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34029222780964834031933299 51043834171447251047899949)
                ·
                  refine ⟨19141437814292719142962481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51043834171447251047899949 19141437814292719142962481)
                  ·
                    refine ⟨14356078360719539357221861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19141437814292719142962481 14356078360719539357221861)
                    ·
                      refine ⟨2691764692634913629479099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14356078360719539357221861 2691764692634913629479099)
                      ·
                        rfl

theorem cell23_5242193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_5242193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242193 prefixEnd_5242193 := by exact prefixLift 5242193
  have htrace : WordTrace (prefixWord ++ tailWord_5242193) baseStart_5242193 baseEnd_5242193 := by
    simpa [prefixWord, tailWord_5242193, baseEnd_5242193] using wordTrace_append hprefix tailTrace_5242193
  have hstable : (prefixWord ++ tailWord_5242193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242193).length < 2 ^ (prefixWord ++ tailWord_5242193).sum := by decide
  have hdescent : baseEnd_5242193 < baseStart_5242193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242200 : List Nat := [2, 1, 2, 2, 1, 1, 3, 5, 1, 2, 3]
def baseStart_5242200 : Nat := 118140960795 + 5242200 * 2 ^ 59
def prefixEnd_5242200 : Nat := 4983230072969 + 3 ^ 40 * 5242200 * 2
def baseEnd_5242200 : Nat := 2691768286999495102091567

theorem tailTrace_5242200 : CollatzResearch.WordTrace tailWord_5242200 prefixEnd_5242200 2691768286999495102091567 := by
  unfold tailWord_5242200
  simp only [CollatzResearch.WordTrace]
  refine ⟨95599370804206085663458027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127465827738941447551277369 95599370804206085663458027)
  ·
    refine ⟨143399056206309128495187041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95599370804206085663458027 143399056206309128495187041)
    ·
      refine ⟨107549292154731846371390281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143399056206309128495187041 107549292154731846371390281)
      ·
        refine ⟨80661969116048884778542711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107549292154731846371390281 80661969116048884778542711)
        ·
          refine ⟨120992953674073327167814067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80661969116048884778542711 120992953674073327167814067)
          ·
            refine ⟨181489430511109990751721101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120992953674073327167814067 181489430511109990751721101)
            ·
              refine ⟨68058536441666246531895413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181489430511109990751721101 68058536441666246531895413)
              ·
                refine ⟨6380487791406210612365195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68058536441666246531895413 6380487791406210612365195)
                ·
                  refine ⟨9570731687109315918547793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6380487791406210612365195 9570731687109315918547793)
                  ·
                    refine ⟨7178048765331986938910845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9570731687109315918547793 7178048765331986938910845)
                    ·
                      refine ⟨2691768286999495102091567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7178048765331986938910845 2691768286999495102091567)
                      ·
                        rfl

theorem cell23_5242200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_5242200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242200 prefixEnd_5242200 := by exact prefixLift 5242200
  have htrace : WordTrace (prefixWord ++ tailWord_5242200) baseStart_5242200 baseEnd_5242200 := by
    simpa [prefixWord, tailWord_5242200, baseEnd_5242200] using wordTrace_append hprefix tailTrace_5242200
  have hstable : (prefixWord ++ tailWord_5242200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242200).length < 2 ^ (prefixWord ++ tailWord_5242200).sum := by decide
  have hdescent : baseEnd_5242200 < baseStart_5242200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242263 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 2, 6]
def baseStart_5242263 : Nat := 118140960795 + 5242263 * 2 ^ 59
def prefixEnd_5242263 : Nat := 4983230072969 + 3 ^ 40 * 5242263 * 2
def baseEnd_5242263 : Nat := 897266878760242785201259

theorem tailTrace_5242263 : CollatzResearch.WordTrace tailWord_5242263 prefixEnd_5242263 897266878760242785201259 := by
  unfold tailWord_5242263
  simp only [CollatzResearch.WordTrace]
  refine ⟨191201039407183933086459443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127467359604789288724306295 191201039407183933086459443)
  ·
    refine ⟨286801559110775899629689165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191201039407183933086459443 286801559110775899629689165)
    ·
      refine ⟨107550584666540962361133437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286801559110775899629689165 107550584666540962361133437)
      ·
        refine ⟨40331469249952860885425039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107550584666540962361133437 40331469249952860885425039)
        ·
          refine ⟨60497203874929291328137559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40331469249952860885425039 60497203874929291328137559)
          ·
            refine ⟨90745805812393936992206339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60497203874929291328137559 90745805812393936992206339)
            ·
              refine ⟨136118708718590905488309509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90745805812393936992206339 136118708718590905488309509)
              ·
                refine ⟨25522257884735794779058033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136118708718590905488309509 25522257884735794779058033)
                ·
                  refine ⟨19141693413551846084293525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25522257884735794779058033 19141693413551846084293525)
                  ·
                    refine ⟨897266878760242785201259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19141693413551846084293525 897266878760242785201259)
                    ·
                      rfl

theorem cell23_5242263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_5242263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242263 prefixEnd_5242263 := by exact prefixLift 5242263
  have htrace : WordTrace (prefixWord ++ tailWord_5242263) baseStart_5242263 baseEnd_5242263 := by
    simpa [prefixWord, tailWord_5242263, baseEnd_5242263] using wordTrace_append hprefix tailTrace_5242263
  have hstable : (prefixWord ++ tailWord_5242263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242263).length < 2 ^ (prefixWord ++ tailWord_5242263).sum := by decide
  have hdescent : baseEnd_5242263 < baseStart_5242263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242308 : List Nat := [2, 3, 3, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_5242308 : Nat := 118140960795 + 5242308 * 2 ^ 59
def prefixEnd_5242308 : Nat := 4983230072969 + 3 ^ 40 * 5242308 * 2
def baseEnd_5242308 : Nat := 2691823742910180679541071

theorem tailTrace_5242308 : CollatzResearch.WordTrace tailWord_5242308 prefixEnd_5242308 2691823742910180679541071 := by
  unfold tailWord_5242308
  simp only [CollatzResearch.WordTrace]
  refine ⟨95601340346010452885923789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127468453794680603847898385 95601340346010452885923789)
  ·
    refine ⟨35850502629753919832221421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95601340346010452885923789 35850502629753919832221421)
    ·
      refine ⟨13443938486157719937083033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35850502629753919832221421 13443938486157719937083033)
      ·
        refine ⟨10082953864618289952812275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13443938486157719937083033 10082953864618289952812275)
        ·
          refine ⟨15124430796927434929218413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10082953864618289952812275 15124430796927434929218413)
          ·
            refine ⟨5671661548847788098456905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15124430796927434929218413 5671661548847788098456905)
            ·
              refine ⟨4253746161635841073842679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5671661548847788098456905 4253746161635841073842679)
              ·
                refine ⟨6380619242453761610764019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4253746161635841073842679 6380619242453761610764019)
                ·
                  refine ⟨9570928863680642416146029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6380619242453761610764019 9570928863680642416146029)
                  ·
                    refine ⟨3589098323880240906054761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9570928863680642416146029 3589098323880240906054761)
                    ·
                      refine ⟨2691823742910180679541071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3589098323880240906054761 2691823742910180679541071)
                      ·
                        rfl

theorem cell23_5242308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_5242308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242308 prefixEnd_5242308 := by exact prefixLift 5242308
  have htrace : WordTrace (prefixWord ++ tailWord_5242308) baseStart_5242308 baseEnd_5242308 := by
    simpa [prefixWord, tailWord_5242308, baseEnd_5242308] using wordTrace_append hprefix tailTrace_5242308
  have hstable : (prefixWord ++ tailWord_5242308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242308).length < 2 ^ (prefixWord ++ tailWord_5242308).sum := by decide
  have hdescent : baseEnd_5242308 < baseStart_5242308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242357 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 1, 7]
def baseStart_5242357 : Nat := 118140960795 + 5242357 * 2 ^ 59
def prefixEnd_5242357 : Nat := 4983230072969 + 3 ^ 40 * 5242357 * 2
def baseEnd_5242357 : Nat := 897282967820750329276115

theorem tailTrace_5242357 : CollatzResearch.WordTrace tailWord_5242357 prefixEnd_5242357 897282967820750329276115 := by
  unfold tailWord_5242357
  simp only [CollatzResearch.WordTrace]
  refine ⟨191204467868843387140381325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127469645245895591426920883 191204467868843387140381325)
  ·
    refine ⟨71701675450816270177642997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191204467868843387140381325 71701675450816270177642997)
    ·
      refine ⟨6722032073514025329154031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71701675450816270177642997 6722032073514025329154031)
      ·
        refine ⟨10083048110271037993731047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6722032073514025329154031 10083048110271037993731047)
        ·
          refine ⟨15124572165406556990596571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10083048110271037993731047 15124572165406556990596571)
          ·
            refine ⟨22686858248109835485894857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15124572165406556990596571 22686858248109835485894857)
            ·
              refine ⟨17015143686082376614421143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22686858248109835485894857 17015143686082376614421143)
              ·
                refine ⟨25522715529123564921631715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17015143686082376614421143 25522715529123564921631715)
                ·
                  refine ⟨38284073293685347382447573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25522715529123564921631715 38284073293685347382447573)
                  ·
                    refine ⟨897282967820750329276115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38284073293685347382447573 897282967820750329276115)
                    ·
                      rfl

theorem cell23_5242357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_5242357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242357 prefixEnd_5242357 := by exact prefixLift 5242357
  have htrace : WordTrace (prefixWord ++ tailWord_5242357) baseStart_5242357 baseEnd_5242357 := by
    simpa [prefixWord, tailWord_5242357, baseEnd_5242357] using wordTrace_append hprefix tailTrace_5242357
  have hstable : (prefixWord ++ tailWord_5242357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242357).length < 2 ^ (prefixWord ++ tailWord_5242357).sum := by decide
  have hdescent : baseEnd_5242357 < baseStart_5242357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242360 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_5242360 : Nat := 118140960795 + 5242360 * 2 ^ 59
def prefixEnd_5242360 : Nat := 4983230072969 + 3 ^ 40 * 5242360 * 2
def baseEnd_5242360 : Nat := 2691850443904214476090831

theorem tailTrace_5242360 : CollatzResearch.WordTrace tailWord_5242360 prefixEnd_5242360 2691850443904214476090831 := by
  unfold tailWord_5242360
  simp only [CollatzResearch.WordTrace]
  refine ⟨95602288643916259326370267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127469718191888345768493689 95602288643916259326370267)
  ·
    refine ⟨143403432965874388989555401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95602288643916259326370267 143403432965874388989555401)
    ·
      refine ⟨107552574724405791742166551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143403432965874388989555401 107552574724405791742166551)
      ·
        refine ⟨161328862086608687613249827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107552574724405791742166551 161328862086608687613249827)
        ·
          refine ⟨241993293129913031419874741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161328862086608687613249827 241993293129913031419874741)
          ·
            refine ⟨22686871230929346695613257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 241993293129913031419874741 22686871230929346695613257)
            ·
              refine ⟨17015153423197010021709943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22686871230929346695613257 17015153423197010021709943)
              ·
                refine ⟨25522730134795515032564915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17015153423197010021709943 25522730134795515032564915)
                ·
                  refine ⟨38284095202193272548847373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25522730134795515032564915 38284095202193272548847373)
                  ·
                    refine ⟨14356535700822477205817765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38284095202193272548847373 14356535700822477205817765)
                    ·
                      refine ⟨2691850443904214476090831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14356535700822477205817765 2691850443904214476090831)
                      ·
                        rfl

theorem cell23_5242360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_5242360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242360 prefixEnd_5242360 := by exact prefixLift 5242360
  have htrace : WordTrace (prefixWord ++ tailWord_5242360) baseStart_5242360 baseEnd_5242360 := by
    simpa [prefixWord, tailWord_5242360, baseEnd_5242360] using wordTrace_append hprefix tailTrace_5242360
  have hstable : (prefixWord ++ tailWord_5242360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242360).length < 2 ^ (prefixWord ++ tailWord_5242360).sum := by decide
  have hdescent : baseEnd_5242360 < baseStart_5242360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242383 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 12]
def baseStart_5242383 : Nat := 118140960795 + 5242383 * 2 ^ 59
def prefixEnd_5242383 : Nat := 4983230072969 + 3 ^ 40 * 5242383 * 2
def baseEnd_5242383 : Nat := 299095805995474209567025

theorem tailTrace_5242383 : CollatzResearch.WordTrace tailWord_5242383 prefixEnd_5242383 299095805995474209567025 := by
  unfold tailWord_5242383
  simp only [CollatzResearch.WordTrace]
  refine ⟨191205416166749193580827803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127470277444499462387218535 191205416166749193580827803)
  ·
    refine ⟨286808124250123790371241705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191205416166749193580827803 286808124250123790371241705)
    ·
      refine ⟨215106093187592842778431279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286808124250123790371241705 215106093187592842778431279)
      ·
        refine ⟨322659139781389264167646919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215106093187592842778431279 322659139781389264167646919)
        ·
          refine ⟨483988709672083896251470379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322659139781389264167646919 483988709672083896251470379)
          ·
            refine ⟨725983064508125844377205569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483988709672083896251470379 725983064508125844377205569)
            ·
              refine ⟨544487298381094383282904177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725983064508125844377205569 544487298381094383282904177)
              ·
                refine ⟨408365473785820787462178133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544487298381094383282904177 408365473785820787462178133)
                ·
                  refine ⟨299095805995474209567025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 408365473785820787462178133 299095805995474209567025)
                  ·
                    rfl

theorem cell23_5242383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 12].length) (baseStart_5242383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242383 prefixEnd_5242383 := by exact prefixLift 5242383
  have htrace : WordTrace (prefixWord ++ tailWord_5242383) baseStart_5242383 baseEnd_5242383 := by
    simpa [prefixWord, tailWord_5242383, baseEnd_5242383] using wordTrace_append hprefix tailTrace_5242383
  have hstable : (prefixWord ++ tailWord_5242383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242383).length < 2 ^ (prefixWord ++ tailWord_5242383).sum := by decide
  have hdescent : baseEnd_5242383 < baseStart_5242383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242387 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 3, 4]
def baseStart_5242387 : Nat := 118140960795 + 5242387 * 2 ^ 59
def prefixEnd_5242387 : Nat := 4983230072969 + 3 ^ 40 * 5242387 * 2
def baseEnd_5242387 : Nat := 897288102627295290151069

theorem tailTrace_5242387 : CollatzResearch.WordTrace tailWord_5242387 prefixEnd_5242387 897288102627295290151069 := by
  unfold tailWord_5242387
  simp only [CollatzResearch.WordTrace]
  refine ⟨191205562058734702263973415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127470374705823134842648943 191205562058734702263973415)
  ·
    refine ⟨286808343088102053395960123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191205562058734702263973415 286808343088102053395960123)
    ·
      refine ⟨430212514632153080093940185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286808343088102053395960123 430212514632153080093940185)
      ·
        refine ⟨322659385974114810070455139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430212514632153080093940185 322659385974114810070455139)
        ·
          refine ⟨483989078961172215105682709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322659385974114810070455139 483989078961172215105682709)
          ·
            refine ⟨22686988076304947583078877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 483989078961172215105682709 22686988076304947583078877)
            ·
              refine ⟨8507620528614355343654579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22686988076304947583078877 8507620528614355343654579)
              ·
                refine ⟨12761430792921533015481869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8507620528614355343654579 12761430792921533015481869)
                ·
                  refine ⟨4785536547345574880805701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12761430792921533015481869 4785536547345574880805701)
                  ·
                    refine ⟨897288102627295290151069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4785536547345574880805701 897288102627295290151069)
                    ·
                      rfl

theorem cell23_5242387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 4].length) (baseStart_5242387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242387 prefixEnd_5242387 := by exact prefixLift 5242387
  have htrace : WordTrace (prefixWord ++ tailWord_5242387) baseStart_5242387 baseEnd_5242387 := by
    simpa [prefixWord, tailWord_5242387, baseEnd_5242387] using wordTrace_append hprefix tailTrace_5242387
  have hstable : (prefixWord ++ tailWord_5242387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242387).length < 2 ^ (prefixWord ++ tailWord_5242387).sum := by decide
  have hdescent : baseEnd_5242387 < baseStart_5242387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242397 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_5242397 : Nat := 118140960795 + 5242397 * 2 ^ 59
def prefixEnd_5242397 : Nat := 4983230072969 + 3 ^ 40 * 5242397 * 2
def baseEnd_5242397 : Nat := 2691869442688430831328161

theorem tailTrace_5242397 : CollatzResearch.WordTrace tailWord_5242397 prefixEnd_5242397 2691869442688430831328161 := by
  unfold tailWord_5242397
  simp only [CollatzResearch.WordTrace]
  refine ⟨191205926788698473971837445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127470617859132315981224963 191205926788698473971837445)
  ·
    refine ⟨35851111272880963869719521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191205926788698473971837445 35851111272880963869719521)
    ·
      refine ⟨26888333454660722902289641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35851111272880963869719521 26888333454660722902289641)
      ·
        refine ⟨20166250090995542176717231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26888333454660722902289641 20166250090995542176717231)
        ·
          refine ⟨30249375136493313265075847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20166250090995542176717231 30249375136493313265075847)
          ·
            refine ⟨45374062704739969897613771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30249375136493313265075847 45374062704739969897613771)
            ·
              refine ⟨68061094057109954846420657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45374062704739969897613771 68061094057109954846420657)
              ·
                refine ⟨51045820542832466134815493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68061094057109954846420657 51045820542832466134815493)
                ·
                  refine ⟨9571091351781087400277905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51045820542832466134815493 9571091351781087400277905)
                  ·
                    refine ⟨7178318513835815550208429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9571091351781087400277905 7178318513835815550208429)
                    ·
                      refine ⟨2691869442688430831328161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7178318513835815550208429 2691869442688430831328161)
                      ·
                        rfl

theorem cell23_5242397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_5242397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242397 prefixEnd_5242397 := by exact prefixLift 5242397
  have htrace : WordTrace (prefixWord ++ tailWord_5242397) baseStart_5242397 baseEnd_5242397 := by
    simpa [prefixWord, tailWord_5242397, baseEnd_5242397] using wordTrace_append hprefix tailTrace_5242397
  have hstable : (prefixWord ++ tailWord_5242397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242397).length < 2 ^ (prefixWord ++ tailWord_5242397).sum := by decide
  have hdescent : baseEnd_5242397 < baseStart_5242397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242414 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_5242414 : Nat := 118140960795 + 5242414 * 2 ^ 59
def prefixEnd_5242414 : Nat := 4983230072969 + 3 ^ 40 * 5242414 * 2
def baseEnd_5242414 : Nat := 2691878171859557264815583

theorem tailTrace_5242414 : CollatzResearch.WordTrace tailWord_5242414 prefixEnd_5242414 2691878171859557264815583 := by
  unfold tailWord_5242414
  simp only [CollatzResearch.WordTrace]
  refine ⟨23900818353704610734400787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127471031219757923916804197 23900818353704610734400787)
  ·
    refine ⟨35851227530556916101601181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23900818353704610734400787 35851227530556916101601181)
    ·
      refine ⟨13444210323958843538100443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35851227530556916101601181 13444210323958843538100443)
      ·
        refine ⟨20166315485938265307150665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13444210323958843538100443 20166315485938265307150665)
        ·
          refine ⟨15124736614453698980362999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20166315485938265307150665 15124736614453698980362999)
          ·
            refine ⟨22687104921680548470544499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15124736614453698980362999 22687104921680548470544499)
            ·
              refine ⟨34030657382520822705816749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22687104921680548470544499 34030657382520822705816749)
              ·
                refine ⟨12761496518445308514681281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34030657382520822705816749 12761496518445308514681281)
                ·
                  refine ⟨9571122388833981386010961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12761496518445308514681281 9571122388833981386010961)
                  ·
                    refine ⟨7178341791625486039508221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9571122388833981386010961 7178341791625486039508221)
                    ·
                      refine ⟨2691878171859557264815583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7178341791625486039508221 2691878171859557264815583)
                      ·
                        rfl

theorem cell23_5242414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_5242414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242414 prefixEnd_5242414 := by exact prefixLift 5242414
  have htrace : WordTrace (prefixWord ++ tailWord_5242414) baseStart_5242414 baseEnd_5242414 := by
    simpa [prefixWord, tailWord_5242414, baseEnd_5242414] using wordTrace_append hprefix tailTrace_5242414
  have hstable : (prefixWord ++ tailWord_5242414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242414).length < 2 ^ (prefixWord ++ tailWord_5242414).sum := by decide
  have hdescent : baseEnd_5242414 < baseStart_5242414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242467 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 4]
def baseStart_5242467 : Nat := 118140960795 + 5242467 * 2 ^ 59
def prefixEnd_5242467 : Nat := 4983230072969 + 3 ^ 40 * 5242467 * 2
def baseEnd_5242467 : Nat := 2691905386334245557452839

theorem tailTrace_5242467 : CollatzResearch.WordTrace tailWord_5242467 prefixEnd_5242467 2691905386334245557452839 := by
  unfold tailWord_5242467
  simp only [CollatzResearch.WordTrace]
  refine ⟨191208479898444875926885655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127472319932296583951257103 191208479898444875926885655)
  ·
    refine ⟨286812719847667313890328483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191208479898444875926885655 286812719847667313890328483)
    ·
      refine ⟨430219079771500970835492725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286812719847667313890328483 430219079771500970835492725)
      ·
        refine ⟨40333038728578216015827443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 430219079771500970835492725 40333038728578216015827443)
        ·
          refine ⟨60499558092867324023741165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40333038728578216015827443 60499558092867324023741165)
          ·
            refine ⟨22687334284825246508902937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60499558092867324023741165 22687334284825246508902937)
            ·
              refine ⟨17015500713618934881677203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22687334284825246508902937 17015500713618934881677203)
              ·
                refine ⟨25523251070428402322515805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17015500713618934881677203 25523251070428402322515805)
                ·
                  refine ⟨9571219151410650870943427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25523251070428402322515805 9571219151410650870943427)
                  ·
                    refine ⟨14356828727115976306415141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9571219151410650870943427 14356828727115976306415141)
                    ·
                      refine ⟨2691905386334245557452839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14356828727115976306415141 2691905386334245557452839)
                      ·
                        rfl

theorem cell23_5242467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_5242467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242467 prefixEnd_5242467 := by exact prefixLift 5242467
  have htrace : WordTrace (prefixWord ++ tailWord_5242467) baseStart_5242467 baseEnd_5242467 := by
    simpa [prefixWord, tailWord_5242467, baseEnd_5242467] using wordTrace_append hprefix tailTrace_5242467
  have hstable : (prefixWord ++ tailWord_5242467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242467).length < 2 ^ (prefixWord ++ tailWord_5242467).sum := by decide
  have hdescent : baseEnd_5242467 < baseStart_5242467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242501 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 3, 2, 2]
def baseStart_5242501 : Nat := 118140960795 + 5242501 * 2 ^ 59
def prefixEnd_5242501 : Nat := 4983230072969 + 3 ^ 40 * 5242501 * 2
def baseEnd_5242501 : Nat := 2691922844676498424427683

theorem tailTrace_5242501 : CollatzResearch.WordTrace tailWord_5242501 prefixEnd_5242501 2691922844676498424427683 := by
  unfold tailWord_5242501
  simp only [CollatzResearch.WordTrace]
  refine ⟨191209719980321699733623357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127473146653547799822415571 191209719980321699733623357)
  ·
    refine ⟨71703644992620637400108759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191209719980321699733623357 71703644992620637400108759)
    ·
      refine ⟨107555467488930956100163139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71703644992620637400108759 107555467488930956100163139)
      ·
        refine ⟨161333201233396434150244709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107555467488930956100163139 161333201233396434150244709)
        ·
          refine ⟨30249975231261831403170883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161333201233396434150244709 30249975231261831403170883)
          ·
            refine ⟨45374962846892747104756325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30249975231261831403170883 45374962846892747104756325)
            ·
              refine ⟨8507805533792390082141811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45374962846892747104756325 8507805533792390082141811)
              ·
                refine ⟨12761708300688585123212717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8507805533792390082141811 12761708300688585123212717)
                ·
                  refine ⟨4785640612758219421204769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12761708300688585123212717 4785640612758219421204769)
                  ·
                    refine ⟨3589230459568664565903577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4785640612758219421204769 3589230459568664565903577)
                    ·
                      refine ⟨2691922844676498424427683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3589230459568664565903577 2691922844676498424427683)
                      ·
                        rfl

theorem cell23_5242501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 2, 2].length) (baseStart_5242501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242501 prefixEnd_5242501 := by exact prefixLift 5242501
  have htrace : WordTrace (prefixWord ++ tailWord_5242501) baseStart_5242501 baseEnd_5242501 := by
    simpa [prefixWord, tailWord_5242501, baseEnd_5242501] using wordTrace_append hprefix tailTrace_5242501
  have hstable : (prefixWord ++ tailWord_5242501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242501).length < 2 ^ (prefixWord ++ tailWord_5242501).sum := by decide
  have hdescent : baseEnd_5242501 < baseStart_5242501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242514 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_5242514 : Nat := 118140960795 + 5242514 * 2 ^ 59
def prefixEnd_5242514 : Nat := 4983230072969 + 3 ^ 40 * 5242514 * 2
def baseEnd_5242514 : Nat := 2691929519925006873565123

theorem tailTrace_5242514 : CollatzResearch.WordTrace tailWord_5242514 prefixEnd_5242514 2691929519925006873565123 := by
  unfold tailWord_5242514
  simp only [CollatzResearch.WordTrace]
  refine ⟨47802548532318650738461649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127473462752849735302564397 47802548532318650738461649)
  ·
    refine ⟨35851911399238988053846237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47802548532318650738461649 35851911399238988053846237)
    ·
      refine ⟨13444466774714620520192339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35851911399238988053846237 13444466774714620520192339)
      ·
        refine ⟨20166700162071930780288509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13444466774714620520192339 20166700162071930780288509)
        ·
          refine ⟨7562512560776974042608191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20166700162071930780288509 7562512560776974042608191)
          ·
            refine ⟨11343768841165461063912287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7562512560776974042608191 11343768841165461063912287)
            ·
              refine ⟨17015653261748191595868431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11343768841165461063912287 17015653261748191595868431)
              ·
                refine ⟨25523479892622287393802647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17015653261748191595868431 25523479892622287393802647)
                ·
                  refine ⟨38285219838933431090703971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25523479892622287393802647 38285219838933431090703971)
                  ·
                    refine ⟨57427829758400146636055957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38285219838933431090703971 57427829758400146636055957)
                    ·
                      refine ⟨2691929519925006873565123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57427829758400146636055957 2691929519925006873565123)
                      ·
                        rfl

theorem cell23_5242514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_5242514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242514 prefixEnd_5242514 := by exact prefixLift 5242514
  have htrace : WordTrace (prefixWord ++ tailWord_5242514) baseStart_5242514 baseEnd_5242514 := by
    simpa [prefixWord, tailWord_5242514, baseEnd_5242514] using wordTrace_append hprefix tailTrace_5242514
  have hstable : (prefixWord ++ tailWord_5242514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242514).length < 2 ^ (prefixWord ++ tailWord_5242514).sum := by decide
  have hdescent : baseEnd_5242514 < baseStart_5242514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242540 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_5242540 : Nat := 118140960795 + 5242540 * 2 ^ 59
def prefixEnd_5242540 : Nat := 4983230072969 + 3 ^ 40 * 5242540 * 2
def baseEnd_5242540 : Nat := 2691942870422023771840003

theorem tailTrace_5242540 : CollatzResearch.WordTrace tailWord_5242540 prefixEnd_5242540 2691942870422023771840003 := by
  unfold tailWord_5242540
  simp only [CollatzResearch.WordTrace]
  refine ⟨95605571213590204697146537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127474094951453606262862049 95605571213590204697146537)
  ·
    refine ⟨71704178410192653522859903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95605571213590204697146537 71704178410192653522859903)
    ·
      refine ⟨107556267615288980284289855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71704178410192653522859903 107556267615288980284289855)
      ·
        refine ⟨161334401422933470426434783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107556267615288980284289855 161334401422933470426434783)
        ·
          refine ⟨242001602134400205639652175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161334401422933470426434783 242001602134400205639652175)
          ·
            refine ⟨363002403201600308459478263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242001602134400205639652175 363002403201600308459478263)
            ·
              refine ⟨544503604802400462689217395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363002403201600308459478263 544503604802400462689217395)
              ·
                refine ⟨816755407203600694033826093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544503604802400462689217395 816755407203600694033826093)
                ·
                  refine ⟨306283277701350260262684785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816755407203600694033826093 306283277701350260262684785)
                  ·
                    refine ⟨229712458276012695197013589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 306283277701350260262684785 229712458276012695197013589)
                    ·
                      refine ⟨2691942870422023771840003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 229712458276012695197013589 2691942870422023771840003)
                      ·
                        rfl

theorem cell23_5242540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_5242540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242540 prefixEnd_5242540 := by exact prefixLift 5242540
  have htrace : WordTrace (prefixWord ++ tailWord_5242540) baseStart_5242540 baseEnd_5242540 := by
    simpa [prefixWord, tailWord_5242540, baseEnd_5242540] using wordTrace_append hprefix tailTrace_5242540
  have hstable : (prefixWord ++ tailWord_5242540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242540).length < 2 ^ (prefixWord ++ tailWord_5242540).sum := by decide
  have hdescent : baseEnd_5242540 < baseStart_5242540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242557 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_5242557 : Nat := 118140960795 + 5242557 * 2 ^ 59
def prefixEnd_5242557 : Nat := 4983230072969 + 3 ^ 40 * 5242557 * 2
def baseEnd_5242557 : Nat := 2691951599593150205327425

theorem tailTrace_5242557 : CollatzResearch.WordTrace tailWord_5242557 prefixEnd_5242557 2691951599593150205327425 := by
  unfold tailWord_5242557
  simp only [CollatzResearch.WordTrace]
  refine ⟨191211762468118821297661925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127474508312079214198441283 191211762468118821297661925)
  ·
    refine ⟨35852205462772278993311611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191211762468118821297661925 35852205462772278993311611)
    ·
      refine ⟨53778308194158418489967417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35852205462772278993311611 53778308194158418489967417)
      ·
        refine ⟨40333731145618813867475563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53778308194158418489967417 40333731145618813867475563)
        ·
          refine ⟨60500596718428220801213345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40333731145618813867475563 60500596718428220801213345)
          ·
            refine ⟨45375447538821165600910009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60500596718428220801213345 45375447538821165600910009)
            ·
              refine ⟨34031585654115874200682507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45375447538821165600910009 34031585654115874200682507)
              ·
                refine ⟨51047378481173811301023761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34031585654115874200682507 51047378481173811301023761)
                ·
                  refine ⟨38285533860880358475767821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51047378481173811301023761 38285533860880358475767821)
                  ·
                    refine ⟨14357075197830134428412933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38285533860880358475767821 14357075197830134428412933)
                    ·
                      refine ⟨2691951599593150205327425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14357075197830134428412933 2691951599593150205327425)
                      ·
                        rfl

theorem cell23_5242557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_5242557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242557 prefixEnd_5242557 := by exact prefixLift 5242557
  have htrace : WordTrace (prefixWord ++ tailWord_5242557) baseStart_5242557 baseEnd_5242557 := by
    simpa [prefixWord, tailWord_5242557, baseEnd_5242557] using wordTrace_append hprefix tailTrace_5242557
  have hstable : (prefixWord ++ tailWord_5242557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242557).length < 2 ^ (prefixWord ++ tailWord_5242557).sum := by decide
  have hdescent : baseEnd_5242557 < baseStart_5242557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242577 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_5242577 : Nat := 118140960795 + 5242577 * 2 ^ 59
def prefixEnd_5242577 : Nat := 4983230072969 + 3 ^ 40 * 5242577 * 2
def baseEnd_5242577 : Nat := 2691961869206240127077333

theorem tailTrace_5242577 : CollatzResearch.WordTrace tailWord_5242577 prefixEnd_5242577 2691961869206240127077333 := by
  unfold tailWord_5242577
  simp only [CollatzResearch.WordTrace]
  refine ⟨191212491928046364713389985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127474994618697576475593323 191212491928046364713389985)
  ·
    refine ⟨143409368946034773535042489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191212491928046364713389985 143409368946034773535042489)
    ·
      refine ⟨107557026709526080151281867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143409368946034773535042489 107557026709526080151281867)
      ·
        refine ⟨161335540064289120226922801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107557026709526080151281867 161335540064289120226922801)
        ·
          refine ⟨121001655048216840170192101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161335540064289120226922801 121001655048216840170192101)
          ·
            refine ⟨22687810321540657531911019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121001655048216840170192101 22687810321540657531911019)
            ·
              refine ⟨34031715482310986297866529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22687810321540657531911019 34031715482310986297866529)
              ·
                refine ⟨25523786611733239723399897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34031715482310986297866529 25523786611733239723399897)
                ·
                  refine ⟨19142839958799929792549923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25523786611733239723399897 19142839958799929792549923)
                  ·
                    refine ⟨28714259938199894688824885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19142839958799929792549923 28714259938199894688824885)
                    ·
                      refine ⟨2691961869206240127077333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28714259938199894688824885 2691961869206240127077333)
                      ·
                        rfl

theorem cell23_5242577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_5242577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242577 prefixEnd_5242577 := by exact prefixLift 5242577
  have htrace : WordTrace (prefixWord ++ tailWord_5242577) baseStart_5242577 baseEnd_5242577 := by
    simpa [prefixWord, tailWord_5242577, baseEnd_5242577] using wordTrace_append hprefix tailTrace_5242577
  have hstable : (prefixWord ++ tailWord_5242577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242577).length < 2 ^ (prefixWord ++ tailWord_5242577).sum := by decide
  have hdescent : baseEnd_5242577 < baseStart_5242577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242578 : List Nat := [3, 2, 2, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_5242578 : Nat := 118140960795 + 5242578 * 2 ^ 59
def prefixEnd_5242578 : Nat := 4983230072969 + 3 ^ 40 * 5242578 * 2
def baseEnd_5242578 : Nat := 2691962382686894623164829

theorem tailTrace_5242578 : CollatzResearch.WordTrace tailWord_5242578 prefixEnd_5242578 2691962382686894623164829 := by
  unfold tailWord_5242578
  simp only [CollatzResearch.WordTrace]
  refine ⟨47803132100260685471044097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127475018934028494589450925 47803132100260685471044097)
  ·
    refine ⟨35852349075195514103283073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47803132100260685471044097 35852349075195514103283073)
    ·
      refine ⟨26889261806396635577462305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35852349075195514103283073 26889261806396635577462305)
      ·
        refine ⟨20166946354797476683096729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26889261806396635577462305 20166946354797476683096729)
        ·
          refine ⟨15125209766098107512322547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20166946354797476683096729 15125209766098107512322547)
          ·
            refine ⟨22687814649147161268483821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15125209766098107512322547 22687814649147161268483821)
            ·
              refine ⟨8507930493430185475681433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22687814649147161268483821 8507930493430185475681433)
              ·
                refine ⟨6380947870072639106761075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8507930493430185475681433 6380947870072639106761075)
                ·
                  refine ⟨9571421805108958660141613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6380947870072639106761075 9571421805108958660141613)
                  ·
                    refine ⟨3589283176915859497553105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9571421805108958660141613 3589283176915859497553105)
                    ·
                      refine ⟨2691962382686894623164829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3589283176915859497553105 2691962382686894623164829)
                      ·
                        rfl

theorem cell23_5242578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_5242578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242578 prefixEnd_5242578 := by exact prefixLift 5242578
  have htrace : WordTrace (prefixWord ++ tailWord_5242578) baseStart_5242578 baseEnd_5242578 := by
    simpa [prefixWord, tailWord_5242578, baseEnd_5242578] using wordTrace_append hprefix tailTrace_5242578
  have hstable : (prefixWord ++ tailWord_5242578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242578).length < 2 ^ (prefixWord ++ tailWord_5242578).sum := by decide
  have hdescent : baseEnd_5242578 < baseStart_5242578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242595 : List Nat := [1, 1, 1, 7, 2, 1, 3, 1, 1, 3, 2]
def baseStart_5242595 : Nat := 118140960795 + 5242595 * 2 ^ 59
def prefixEnd_5242595 : Nat := 4983230072969 + 3 ^ 40 * 5242595 * 2
def baseEnd_5242595 : Nat := 2691971111858021056652251

theorem tailTrace_5242595 : CollatzResearch.WordTrace tailWord_5242595 prefixEnd_5242595 2691971111858021056652251 := by
  unfold tailWord_5242595
  simp only [CollatzResearch.WordTrace]
  refine ⟨191213148441981153787545239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127475432294654102525030159 191213148441981153787545239)
  ·
    refine ⟨286819722662971730681317859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191213148441981153787545239 286819722662971730681317859)
    ·
      refine ⟨430229583994457596021976789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286819722662971730681317859 430229583994457596021976789)
      ·
        refine ⟨10083505874870099906765081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 430229583994457596021976789 10083505874870099906765081)
        ·
          refine ⟨7562629406152574930073811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10083505874870099906765081 7562629406152574930073811)
          ·
            refine ⟨11343944109228862395110717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7562629406152574930073811 11343944109228862395110717)
            ·
              refine ⟨4253979040960823398166519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11343944109228862395110717 4253979040960823398166519)
              ·
                refine ⟨6380968561441235097249779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4253979040960823398166519 6380968561441235097249779)
                ·
                  refine ⟨9571452842161852645874669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6380968561441235097249779 9571452842161852645874669)
                  ·
                    refine ⟨3589294815810694742203001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9571452842161852645874669 3589294815810694742203001)
                    ·
                      refine ⟨2691971111858021056652251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3589294815810694742203001 2691971111858021056652251)
                      ·
                        rfl

theorem cell23_5242595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_5242595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242595 prefixEnd_5242595 := by exact prefixLift 5242595
  have htrace : WordTrace (prefixWord ++ tailWord_5242595) baseStart_5242595 baseEnd_5242595 := by
    simpa [prefixWord, tailWord_5242595, baseEnd_5242595] using wordTrace_append hprefix tailTrace_5242595
  have hstable : (prefixWord ++ tailWord_5242595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242595).length < 2 ^ (prefixWord ++ tailWord_5242595).sum := by decide
  have hdescent : baseEnd_5242595 < baseStart_5242595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242627 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 4, 5]
def baseStart_5242627 : Nat := 118140960795 + 5242627 * 2 ^ 59
def prefixEnd_5242627 : Nat := 4983230072969 + 3 ^ 40 * 5242627 * 2
def baseEnd_5242627 : Nat := 897329181079654977150701

theorem tailTrace_5242627 : CollatzResearch.WordTrace tailWord_5242627 prefixEnd_5242627 897329181079654977150701 := by
  unfold tailWord_5242627
  simp only [CollatzResearch.WordTrace]
  refine ⟨191214315577865223252710135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127476210385243482168473423 191214315577865223252710135)
  ·
    refine ⟨286821473366797834879065203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191214315577865223252710135 286821473366797834879065203)
    ·
      refine ⟨430232210050196752318597805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286821473366797834879065203 430232210050196752318597805)
      ·
        refine ⟨161337078768823782119474177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430232210050196752318597805 161337078768823782119474177)
        ·
          refine ⟨121002809076617836589605633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161337078768823782119474177 121002809076617836589605633)
          ·
            refine ⟨90752106807463377442204225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121002809076617836589605633 90752106807463377442204225)
            ·
              refine ⟨68064080105597533081653169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90752106807463377442204225 68064080105597533081653169)
              ·
                refine ⟨51048060079198149811239877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68064080105597533081653169 51048060079198149811239877)
                ·
                  refine ⟨9571511264849653089607477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51048060079198149811239877 9571511264849653089607477)
                  ·
                    refine ⟨897329181079654977150701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9571511264849653089607477 897329181079654977150701)
                    ·
                      rfl

theorem cell23_5242627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 5].length) (baseStart_5242627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242627 prefixEnd_5242627 := by exact prefixLift 5242627
  have htrace : WordTrace (prefixWord ++ tailWord_5242627) baseStart_5242627 baseEnd_5242627 := by
    simpa [prefixWord, tailWord_5242627, baseEnd_5242627] using wordTrace_append hprefix tailTrace_5242627
  have hstable : (prefixWord ++ tailWord_5242627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242627).length < 2 ^ (prefixWord ++ tailWord_5242627).sum := by decide
  have hdescent : baseEnd_5242627 < baseStart_5242627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242684 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_5242684 : Nat := 118140960795 + 5242684 * 2 ^ 59
def prefixEnd_5242684 : Nat := 4983230072969 + 3 ^ 40 * 5242684 * 2
def baseEnd_5242684 : Nat := 2692016811636271208439341

theorem tailTrace_5242684 : CollatzResearch.WordTrace tailWord_5242684 prefixEnd_5242684 2692016811636271208439341 := by
  unfold tailWord_5242684
  simp only [CollatzResearch.WordTrace]
  refine ⟨95608197269329360993767553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127477596359105814658356737 95608197269329360993767553)
  ·
    refine ⟨71706147951997020745325665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95608197269329360993767553 71706147951997020745325665)
    ·
      refine ⟨53779610963997765558994249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71706147951997020745325665 53779610963997765558994249)
      ·
        refine ⟨40334708222998324169245687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53779610963997765558994249 40334708222998324169245687)
        ·
          refine ⟨60502062334497486253868531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40334708222998324169245687 60502062334497486253868531)
          ·
            refine ⟨90753093501746229380802797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60502062334497486253868531 90753093501746229380802797)
            ·
              refine ⟨34032410063154836017801049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90753093501746229380802797 34032410063154836017801049)
              ·
                refine ⟨25524307547366127013350787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34032410063154836017801049 25524307547366127013350787)
                ·
                  refine ⟨38286461321049190520026181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25524307547366127013350787 38286461321049190520026181)
                  ·
                    refine ⟨7178711497696723222504909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38286461321049190520026181 7178711497696723222504909)
                    ·
                      refine ⟨2692016811636271208439341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7178711497696723222504909 2692016811636271208439341)
                      ·
                        rfl

theorem cell23_5242684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_5242684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242684 prefixEnd_5242684 := by exact prefixLift 5242684
  have htrace : WordTrace (prefixWord ++ tailWord_5242684) baseStart_5242684 baseEnd_5242684 := by
    simpa [prefixWord, tailWord_5242684, baseEnd_5242684] using wordTrace_append hprefix tailTrace_5242684
  have hstable : (prefixWord ++ tailWord_5242684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242684).length < 2 ^ (prefixWord ++ tailWord_5242684).sum := by decide
  have hdescent : baseEnd_5242684 < baseStart_5242684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242784 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 4]
def baseStart_5242784 : Nat := 118140960795 + 5242784 * 2 ^ 59
def prefixEnd_5242784 : Nat := 4983230072969 + 3 ^ 40 * 5242784 * 2
def baseEnd_5242784 : Nat := 2692068159701720817188881

theorem tailTrace_5242784 : CollatzResearch.WordTrace tailWord_5242784 prefixEnd_5242784 2692068159701720817188881 := by
  unfold tailWord_5242784
  simp only [CollatzResearch.WordTrace]
  refine ⟨95610020919148219533087703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127480027892197626044116937 95610020919148219533087703)
  ·
    refine ⟨143415031378722329299631555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95610020919148219533087703 143415031378722329299631555)
    ·
      refine ⟨215122547068083493949447333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143415031378722329299631555 215122547068083493949447333)
      ·
        refine ⟨40335477575265655115521375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215122547068083493949447333 40335477575265655115521375)
        ·
          refine ⟨60503216362898482673282063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40335477575265655115521375 60503216362898482673282063)
          ·
            refine ⟨90754824544347724009923095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60503216362898482673282063 90754824544347724009923095)
            ·
              refine ⟨136132236816521586014884643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90754824544347724009923095 136132236816521586014884643)
              ·
                refine ⟨204198355224782379022326965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136132236816521586014884643 204198355224782379022326965)
                ·
                  refine ⟨19143595802323348033343153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204198355224782379022326965 19143595802323348033343153)
                  ·
                    refine ⟨14357696851742511025007365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19143595802323348033343153 14357696851742511025007365)
                    ·
                      refine ⟨2692068159701720817188881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14357696851742511025007365 2692068159701720817188881)
                      ·
                        rfl

theorem cell23_5242784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_5242784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242784 prefixEnd_5242784 := by exact prefixLift 5242784
  have htrace : WordTrace (prefixWord ++ tailWord_5242784) baseStart_5242784 baseEnd_5242784 := by
    simpa [prefixWord, tailWord_5242784, baseEnd_5242784] using wordTrace_append hprefix tailTrace_5242784
  have hstable : (prefixWord ++ tailWord_5242784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242784).length < 2 ^ (prefixWord ++ tailWord_5242784).sum := by decide
  have hdescent : baseEnd_5242784 < baseStart_5242784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242801 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_5242801 : Nat := 118140960795 + 5242801 * 2 ^ 59
def prefixEnd_5242801 : Nat := 4983230072969 + 3 ^ 40 * 5242801 * 2
def baseEnd_5242801 : Nat := 2692076888872847250676303

theorem tailTrace_5242801 : CollatzResearch.WordTrace tailWord_5242801 prefixEnd_5242801 2692076888872847250676303 := by
  unfold tailWord_5242801
  simp only [CollatzResearch.WordTrace]
  refine ⟨191220661879234850969544257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127480441252823233979696171 191220661879234850969544257)
  ·
    refine ⟨143415496409426138227158193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191220661879234850969544257 143415496409426138227158193)
    ·
      refine ⟨107561622307069603670368645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143415496409426138227158193 107561622307069603670368645)
      ·
        refine ⟨20167804182575550688194121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107561622307069603670368645 20167804182575550688194121)
        ·
          refine ⟨15125853136931663016145591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20167804182575550688194121 15125853136931663016145591)
          ·
            refine ⟨22688779705397494524218387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15125853136931663016145591 22688779705397494524218387)
            ·
              refine ⟨34033169558096241786327581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22688779705397494524218387 34033169558096241786327581)
              ·
                refine ⟨12762438584286090669872843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34033169558096241786327581 12762438584286090669872843)
                ·
                  refine ⟨19143657876429136004809265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12762438584286090669872843 19143657876429136004809265)
                  ·
                    refine ⟨14357743407321852003606949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19143657876429136004809265 14357743407321852003606949)
                    ·
                      refine ⟨2692076888872847250676303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14357743407321852003606949 2692076888872847250676303)
                      ·
                        rfl

theorem cell23_5242801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_5242801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242801 prefixEnd_5242801 := by exact prefixLift 5242801
  have htrace : WordTrace (prefixWord ++ tailWord_5242801) baseStart_5242801 baseEnd_5242801 := by
    simpa [prefixWord, tailWord_5242801, baseEnd_5242801] using wordTrace_append hprefix tailTrace_5242801
  have hstable : (prefixWord ++ tailWord_5242801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242801).length < 2 ^ (prefixWord ++ tailWord_5242801).sum := by decide
  have hdescent : baseEnd_5242801 < baseStart_5242801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242805 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_5242805 : Nat := 118140960795 + 5242805 * 2 ^ 59
def prefixEnd_5242805 : Nat := 4983230072969 + 3 ^ 40 * 5242805 * 2
def baseEnd_5242805 : Nat := 2692078942795465235026285

theorem tailTrace_5242805 : CollatzResearch.WordTrace tailWord_5242805 prefixEnd_5242805 2692078942795465235026285 := by
  unfold tailWord_5242805
  simp only [CollatzResearch.WordTrace]
  refine ⟨191220807771220359652689869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127480538514146906435126579 191220807771220359652689869)
  ·
    refine ⟨71707802914207634869758701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191220807771220359652689869 71707802914207634869758701)
    ·
      refine ⟨26890426092827863076159513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71707802914207634869758701 26890426092827863076159513)
      ·
        refine ⟨20167819569620897307119635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26890426092827863076159513 20167819569620897307119635)
        ·
          refine ⟨30251729354431345960679453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20167819569620897307119635 30251729354431345960679453)
          ·
            refine ⟨11344398507911754735254795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30251729354431345960679453 11344398507911754735254795)
            ·
              refine ⟨17016597761867632102882193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11344398507911754735254795 17016597761867632102882193)
              ·
                refine ⟨12762448321400724077161645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17016597761867632102882193 12762448321400724077161645)
                ·
                  refine ⟨4785918120525271528935617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12762448321400724077161645 4785918120525271528935617)
                  ·
                    refine ⟨3589438590393953646701713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4785918120525271528935617 3589438590393953646701713)
                    ·
                      refine ⟨2692078942795465235026285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3589438590393953646701713 2692078942795465235026285)
                      ·
                        rfl

theorem cell23_5242805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_5242805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242805 prefixEnd_5242805 := by exact prefixLift 5242805
  have htrace : WordTrace (prefixWord ++ tailWord_5242805) baseStart_5242805 baseEnd_5242805 := by
    simpa [prefixWord, tailWord_5242805, baseEnd_5242805] using wordTrace_append hprefix tailTrace_5242805
  have hstable : (prefixWord ++ tailWord_5242805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242805).length < 2 ^ (prefixWord ++ tailWord_5242805).sum := by decide
  have hdescent : baseEnd_5242805 < baseStart_5242805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242855 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_5242855 : Nat := 118140960795 + 5242855 * 2 ^ 59
def prefixEnd_5242855 : Nat := 4983230072969 + 3 ^ 40 * 5242855 * 2
def baseEnd_5242855 : Nat := 2692104616828190039401055

theorem tailTrace_5242855 : CollatzResearch.WordTrace tailWord_5242855 prefixEnd_5242855 2692104616828190039401055 := by
  unfold tailWord_5242855
  simp only [CollatzResearch.WordTrace]
  refine ⟨191222631421039218192010019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127481754280692812128006679 191222631421039218192010019)
  ·
    refine ⟨286833947131558827288015029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191222631421039218192010019 286833947131558827288015029)
    ·
      refine ⟨26890682543583640058251409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 286833947131558827288015029 26890682543583640058251409)
      ·
        refine ⟨20168011907687730043688557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26890682543583640058251409 20168011907687730043688557)
        ·
          refine ⟨7563004465382898766383209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20168011907687730043688557 7563004465382898766383209)
          ·
            refine ⟨5672253349037174074787407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7563004465382898766383209 5672253349037174074787407)
            ·
              refine ⟨8508380023555761112181111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5672253349037174074787407 8508380023555761112181111)
              ·
                refine ⟨12762570035333641668271667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8508380023555761112181111 12762570035333641668271667)
                ·
                  refine ⟨19143855053000462502407501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12762570035333641668271667 19143855053000462502407501)
                  ·
                    refine ⟨7178945644875173438402813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19143855053000462502407501 7178945644875173438402813)
                    ·
                      refine ⟨2692104616828190039401055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7178945644875173438402813 2692104616828190039401055)
                      ·
                        rfl

theorem cell23_5242855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_5242855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242855 prefixEnd_5242855 := by exact prefixLift 5242855
  have htrace : WordTrace (prefixWord ++ tailWord_5242855) baseStart_5242855 baseEnd_5242855 := by
    simpa [prefixWord, tailWord_5242855, baseEnd_5242855] using wordTrace_append hprefix tailTrace_5242855
  have hstable : (prefixWord ++ tailWord_5242855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242855).length < 2 ^ (prefixWord ++ tailWord_5242855).sum := by decide
  have hdescent : baseEnd_5242855 < baseStart_5242855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242881 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_5242881 : Nat := 118140960795 + 5242881 * 2 ^ 59
def prefixEnd_5242881 : Nat := 4983230072969 + 3 ^ 40 * 5242881 * 2
def baseEnd_5242881 : Nat := 2692117967325206937675935

theorem tailTrace_5242881 : CollatzResearch.WordTrace tailWord_5242881 prefixEnd_5242881 2692117967325206937675935 := by
  unfold tailWord_5242881
  simp only [CollatzResearch.WordTrace]
  refine ⟨191223579718945024632456497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127482386479296683088304331 191223579718945024632456497)
  ·
    refine ⟨143417684789208768474342373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191223579718945024632456497 143417684789208768474342373)
    ·
      refine ⟨26890815897976644088939195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143417684789208768474342373 26890815897976644088939195)
      ·
        refine ⟨40336223846964966133408793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26890815897976644088939195 40336223846964966133408793)
        ·
          refine ⟨30252167885223724600056595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40336223846964966133408793 30252167885223724600056595)
          ·
            refine ⟨45378251827835586900084893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30252167885223724600056595 45378251827835586900084893)
            ·
              refine ⟨17016844435438345087531835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45378251827835586900084893 17016844435438345087531835)
              ·
                refine ⟨25525266653157517631297753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17016844435438345087531835 25525266653157517631297753)
                ·
                  refine ⟨19143949989868138223473315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25525266653157517631297753 19143949989868138223473315)
                  ·
                    refine ⟨28715924984802207335209973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19143949989868138223473315 28715924984802207335209973)
                    ·
                      refine ⟨2692117967325206937675935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28715924984802207335209973 2692117967325206937675935)
                      ·
                        rfl

theorem cell23_5242881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_5242881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242881 prefixEnd_5242881 := by exact prefixLift 5242881
  have htrace : WordTrace (prefixWord ++ tailWord_5242881) baseStart_5242881 baseEnd_5242881 := by
    simpa [prefixWord, tailWord_5242881, baseEnd_5242881] using wordTrace_append hprefix tailTrace_5242881
  have hstable : (prefixWord ++ tailWord_5242881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242881).length < 2 ^ (prefixWord ++ tailWord_5242881).sum := by decide
  have hdescent : baseEnd_5242881 < baseStart_5242881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242911 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 3]
def baseStart_5242911 : Nat := 118140960795 + 5242911 * 2 ^ 59
def prefixEnd_5242911 : Nat := 4983230072969 + 3 ^ 40 * 5242911 * 2
def baseEnd_5242911 : Nat := 2692133371744841820300797

theorem tailTrace_5242911 : CollatzResearch.WordTrace tailWord_5242911 prefixEnd_5242911 2692133371744841820300797 := by
  unfold tailWord_5242911
  simp only [CollatzResearch.WordTrace]
  refine ⟨191224673908836339756048587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127483115939224226504032391 191224673908836339756048587)
  ·
    refine ⟨286837010863254509634072881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191224673908836339756048587 286837010863254509634072881)
    ·
      refine ⟨215127758147440882225554661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286837010863254509634072881 215127758147440882225554661)
      ·
        refine ⟨40336454652645165417291499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215127758147440882225554661 40336454652645165417291499)
        ·
          refine ⟨60504681978967748125937249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40336454652645165417291499 60504681978967748125937249)
          ·
            refine ⟨45378511484225811094452937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60504681978967748125937249 45378511484225811094452937)
            ·
              refine ⟨34033883613169358320839703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45378511484225811094452937 34033883613169358320839703)
              ·
                refine ⟨51050825419754037481259555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34033883613169358320839703 51050825419754037481259555)
                ·
                  refine ⟨76576238129631056221889333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51050825419754037481259555 76576238129631056221889333)
                  ·
                    refine ⟨7179022324652911520802125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76576238129631056221889333 7179022324652911520802125)
                    ·
                      refine ⟨2692133371744841820300797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7179022324652911520802125 2692133371744841820300797)
                      ·
                        rfl

theorem cell23_5242911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_5242911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242911 prefixEnd_5242911 := by exact prefixLift 5242911
  have htrace : WordTrace (prefixWord ++ tailWord_5242911) baseStart_5242911 baseEnd_5242911 := by
    simpa [prefixWord, tailWord_5242911, baseEnd_5242911] using wordTrace_append hprefix tailTrace_5242911
  have hstable : (prefixWord ++ tailWord_5242911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242911).length < 2 ^ (prefixWord ++ tailWord_5242911).sum := by decide
  have hdescent : baseEnd_5242911 < baseStart_5242911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242931 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 2, 5]
def baseStart_5242931 : Nat := 118140960795 + 5242931 * 2 ^ 59
def prefixEnd_5242931 : Nat := 4983230072969 + 3 ^ 40 * 5242931 * 2
def baseEnd_5242931 : Nat := 897381213785977247350235

theorem tailTrace_5242931 : CollatzResearch.WordTrace tailWord_5242931 prefixEnd_5242931 897381213785977247350235 := by
  unfold tailWord_5242931
  simp only [CollatzResearch.WordTrace]
  refine ⟨191225403368763883171776647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127483602245842588781184431 191225403368763883171776647)
  ·
    refine ⟨286838105053145824757664971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191225403368763883171776647 286838105053145824757664971)
    ·
      refine ⟨430257157579718737136497457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286838105053145824757664971 430257157579718737136497457)
      ·
        refine ⟨322692868184789052852373093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430257157579718737136497457 322692868184789052852373093)
        ·
          refine ⟨60504912784647947409819955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 322692868184789052852373093 60504912784647947409819955)
          ·
            refine ⟨90757369176971921114729933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60504912784647947409819955 90757369176971921114729933)
            ·
              refine ⟨34034013441364470418023725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90757369176971921114729933 34034013441364470418023725)
              ·
                refine ⟨12762755040511676406758897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34034013441364470418023725 12762755040511676406758897)
                ·
                  refine ⟨9572066280383757305069173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12762755040511676406758897 9572066280383757305069173)
                  ·
                    refine ⟨897381213785977247350235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9572066280383757305069173 897381213785977247350235)
                    ·
                      rfl

theorem cell23_5242931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 5].length) (baseStart_5242931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242931 prefixEnd_5242931 := by exact prefixLift 5242931
  have htrace : WordTrace (prefixWord ++ tailWord_5242931) baseStart_5242931 baseEnd_5242931 := by
    simpa [prefixWord, tailWord_5242931, baseEnd_5242931] using wordTrace_append hprefix tailTrace_5242931
  have hstable : (prefixWord ++ tailWord_5242931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242931).length < 2 ^ (prefixWord ++ tailWord_5242931).sum := by decide
  have hdescent : baseEnd_5242931 < baseStart_5242931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242941 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_5242941 : Nat := 118140960795 + 5242941 * 2 ^ 59
def prefixEnd_5242941 : Nat := 4983230072969 + 3 ^ 40 * 5242941 * 2
def baseEnd_5242941 : Nat := 2692148776164476702925659

theorem tailTrace_5242941 : CollatzResearch.WordTrace tailWord_5242941 prefixEnd_5242941 2692148776164476702925659 := by
  unfold tailWord_5242941
  simp only [CollatzResearch.WordTrace]
  refine ⟨191225768098727654879640677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127483845399151769919760451 191225768098727654879640677)
  ·
    refine ⟨35854831518511435289932627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191225768098727654879640677 35854831518511435289932627)
    ·
      refine ⟨53782247277767152934898941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35854831518511435289932627 53782247277767152934898941)
      ·
        refine ⟨20168342729162682350587103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53782247277767152934898941 20168342729162682350587103)
        ·
          refine ⟨30252514093744023525880655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20168342729162682350587103 30252514093744023525880655)
          ·
            refine ⟨45378771140616035288820983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30252514093744023525880655 45378771140616035288820983)
            ·
              refine ⟨68068156710924052933231475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45378771140616035288820983 68068156710924052933231475)
              ·
                refine ⟨102102235066386079399847213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68068156710924052933231475 102102235066386079399847213)
                ·
                  refine ⟨38288338149894779774942705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102102235066386079399847213 38288338149894779774942705)
                  ·
                    refine ⟨28716253612421084831207029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38288338149894779774942705 28716253612421084831207029)
                    ·
                      refine ⟨2692148776164476702925659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28716253612421084831207029 2692148776164476702925659)
                      ·
                        rfl

theorem cell23_5242941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_5242941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242941 prefixEnd_5242941 := by exact prefixLift 5242941
  have htrace : WordTrace (prefixWord ++ tailWord_5242941) baseStart_5242941 baseEnd_5242941 := by
    simpa [prefixWord, tailWord_5242941, baseEnd_5242941] using wordTrace_append hprefix tailTrace_5242941
  have hstable : (prefixWord ++ tailWord_5242941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242941).length < 2 ^ (prefixWord ++ tailWord_5242941).sum := by decide
  have hdescent : baseEnd_5242941 < baseStart_5242941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242968 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 1, 6, 2]
def baseStart_5242968 : Nat := 118140960795 + 5242968 * 2 ^ 59
def prefixEnd_5242968 : Nat := 4983230072969 + 3 ^ 40 * 5242968 * 2
def baseEnd_5242968 : Nat := 2692162640142148097288035

theorem tailTrace_5242968 : CollatzResearch.WordTrace tailWord_5242968 prefixEnd_5242968 2692162640142148097288035 := by
  unfold tailWord_5242968
  simp only [CollatzResearch.WordTrace]
  refine ⟨95613376434814919245436779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127484501913086558993915705 95613376434814919245436779)
  ·
    refine ⟨143420064652222378868155169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95613376434814919245436779 143420064652222378868155169)
    ·
      refine ⟨107565048489166784151116377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143420064652222378868155169 107565048489166784151116377)
      ·
        refine ⟨80673786366875088113337283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107565048489166784151116377 80673786366875088113337283)
        ·
          refine ⟨121010679550312632170005925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80673786366875088113337283 121010679550312632170005925)
          ·
            refine ⟨22689502415683618531876111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121010679550312632170005925 22689502415683618531876111)
            ·
              refine ⟨34034253623525427797814167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22689502415683618531876111 34034253623525427797814167)
              ·
                refine ⟨51051380435288141696721251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34034253623525427797814167 51051380435288141696721251)
                ·
                  refine ⟨76577070652932212545081877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51051380435288141696721251 76577070652932212545081877)
                  ·
                    refine ⟨3589550186856197463050713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76577070652932212545081877 3589550186856197463050713)
                    ·
                      refine ⟨2692162640142148097288035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3589550186856197463050713 2692162640142148097288035)
                      ·
                        rfl

theorem cell23_5242968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_5242968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242968 prefixEnd_5242968 := by exact prefixLift 5242968
  have htrace : WordTrace (prefixWord ++ tailWord_5242968) baseStart_5242968 baseEnd_5242968 := by
    simpa [prefixWord, tailWord_5242968, baseEnd_5242968] using wordTrace_append hprefix tailTrace_5242968
  have hstable : (prefixWord ++ tailWord_5242968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242968).length < 2 ^ (prefixWord ++ tailWord_5242968).sum := by decide
  have hdescent : baseEnd_5242968 < baseStart_5242968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242988 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 3]
def baseStart_5242988 : Nat := 118140960795 + 5242988 * 2 ^ 59
def prefixEnd_5242988 : Nat := 4983230072969 + 3 ^ 40 * 5242988 * 2
def baseEnd_5242988 : Nat := 2692172909755238019037943

theorem tailTrace_5242988 : CollatzResearch.WordTrace tailWord_5242988 prefixEnd_5242988 2692172909755238019037943 := by
  unfold tailWord_5242988
  simp only [CollatzResearch.WordTrace]
  refine ⟨95613741164778690953300809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127484988219704921271067745 95613741164778690953300809)
  ·
    refine ⟨71710305873584018214975607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95613741164778690953300809 71710305873584018214975607)
    ·
      refine ⟨107565458810376027322463411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71710305873584018214975607 107565458810376027322463411)
      ·
        refine ⟨161348188215564040983695117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107565458810376027322463411 161348188215564040983695117)
        ·
          refine ⟨60505570580836515368885669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161348188215564040983695117 60505570580836515368885669)
          ·
            refine ⟨11344794483906846631666063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60505570580836515368885669 11344794483906846631666063)
            ·
              refine ⟨17017191725860269947499095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11344794483906846631666063 17017191725860269947499095)
              ·
                refine ⟨25525787588790404921248643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17017191725860269947499095 25525787588790404921248643)
                ·
                  refine ⟨38288681383185607381872965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25525787588790404921248643 38288681383185607381872965)
                  ·
                    refine ⟨7179127759347301384101181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38288681383185607381872965 7179127759347301384101181)
                    ·
                      refine ⟨2692172909755238019037943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7179127759347301384101181 2692172909755238019037943)
                      ·
                        rfl

theorem cell23_5242988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_5242988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242988 prefixEnd_5242988 := by exact prefixLift 5242988
  have htrace : WordTrace (prefixWord ++ tailWord_5242988) baseStart_5242988 baseEnd_5242988 := by
    simpa [prefixWord, tailWord_5242988, baseEnd_5242988] using wordTrace_append hprefix tailTrace_5242988
  have hstable : (prefixWord ++ tailWord_5242988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242988).length < 2 ^ (prefixWord ++ tailWord_5242988).sum := by decide
  have hdescent : baseEnd_5242988 < baseStart_5242988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5242998 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_5242998 : Nat := 118140960795 + 5242998 * 2 ^ 59
def prefixEnd_5242998 : Nat := 4983230072969 + 3 ^ 40 * 5242998 * 2
def baseEnd_5242998 : Nat := 2692178044561782979912897

theorem tailTrace_5242998 : CollatzResearch.WordTrace tailWord_5242998 prefixEnd_5242998 2692178044561782979912897 := by
  unfold tailWord_5242998
  simp only [CollatzResearch.WordTrace]
  refine ⟨11951740441220072100904103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127485231373014102409643765 11951740441220072100904103)
  ·
    refine ⟨17927610661830108151356155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11951740441220072100904103 17927610661830108151356155)
    ·
      refine ⟨26891415992745162227034233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17927610661830108151356155 26891415992745162227034233)
      ·
        refine ⟨20168561994558871670275675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26891415992745162227034233 20168561994558871670275675)
        ·
          refine ⟨30252842991838307505413513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20168561994558871670275675 30252842991838307505413513)
          ·
            refine ⟨22689632243878730629060135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30252842991838307505413513 22689632243878730629060135)
            ·
              refine ⟨34034448365818095943590203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22689632243878730629060135 34034448365818095943590203)
              ·
                refine ⟨51051672548727143915385305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34034448365818095943590203 51051672548727143915385305)
                ·
                  refine ⟨38288754411545357936538979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51051672548727143915385305 38288754411545357936538979)
                  ·
                    refine ⟨57433131617318036904808469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38288754411545357936538979 57433131617318036904808469)
                    ·
                      refine ⟨2692178044561782979912897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57433131617318036904808469 2692178044561782979912897)
                      ·
                        rfl

theorem cell23_5242998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_5242998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5242998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5242998 prefixEnd_5242998 := by exact prefixLift 5242998
  have htrace : WordTrace (prefixWord ++ tailWord_5242998) baseStart_5242998 baseEnd_5242998 := by
    simpa [prefixWord, tailWord_5242998, baseEnd_5242998] using wordTrace_append hprefix tailTrace_5242998
  have hstable : (prefixWord ++ tailWord_5242998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5242998).length < 2 ^ (prefixWord ++ tailWord_5242998).sum := by decide
  have hdescent : baseEnd_5242998 < baseStart_5242998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5242998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243011 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 6]
def baseStart_5243011 : Nat := 118140960795 + 5243011 * 2 ^ 59
def prefixEnd_5243011 : Nat := 4983230072969 + 3 ^ 40 * 5243011 * 2
def baseEnd_5243011 : Nat := 2692184719810291429050337

theorem tailTrace_5243011 : CollatzResearch.WordTrace tailWord_5243011 prefixEnd_5243011 2692184719810291429050337 := by
  unfold tailWord_5243011
  simp only [CollatzResearch.WordTrace]
  refine ⟨191228321208474056834688887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127485547472316037889792591 191228321208474056834688887)
  ·
    refine ⟨286842481812711085252033331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191228321208474056834688887 286842481812711085252033331)
    ·
      refine ⟨430263722719066627878049997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286842481812711085252033331 430263722719066627878049997)
      ·
        refine ⟨161348896019649985454268749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430263722719066627878049997 161348896019649985454268749)
        ·
          refine ⟨60505836007368744545350781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161348896019649985454268749 60505836007368744545350781)
          ·
            refine ⟨22689688502763279204506543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60505836007368744545350781 22689688502763279204506543)
            ·
              refine ⟨34034532754144918806759815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22689688502763279204506543 34034532754144918806759815)
              ·
                refine ⟨51051799131217378210139723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34034532754144918806759815 51051799131217378210139723)
                ·
                  refine ⟨76577698696826067315209585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51051799131217378210139723 76577698696826067315209585)
                  ·
                    refine ⟨57433274022619550486407189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76577698696826067315209585 57433274022619550486407189)
                    ·
                      refine ⟨2692184719810291429050337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57433274022619550486407189 2692184719810291429050337)
                      ·
                        rfl

theorem cell23_5243011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_5243011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243011 prefixEnd_5243011 := by exact prefixLift 5243011
  have htrace : WordTrace (prefixWord ++ tailWord_5243011) baseStart_5243011 baseEnd_5243011 := by
    simpa [prefixWord, tailWord_5243011, baseEnd_5243011] using wordTrace_append hprefix tailTrace_5243011
  have hstable : (prefixWord ++ tailWord_5243011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243011).length < 2 ^ (prefixWord ++ tailWord_5243011).sum := by decide
  have hdescent : baseEnd_5243011 < baseStart_5243011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243045 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 2, 3, 2]
def baseStart_5243045 : Nat := 118140960795 + 5243045 * 2 ^ 59
def prefixEnd_5243045 : Nat := 4983230072969 + 3 ^ 40 * 5243045 * 2
def baseEnd_5243045 : Nat := 2692202178152544296025181

theorem tailTrace_5243045 : CollatzResearch.WordTrace tailWord_5243045 prefixEnd_5243045 2692202178152544296025181 := by
  unfold tailWord_5243045
  simp only [CollatzResearch.WordTrace]
  refine ⟨191229561290350880641426589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127486374193567253760951059 191229561290350880641426589)
  ·
    refine ⟨71711085483881580240534971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191229561290350880641426589 71711085483881580240534971)
    ·
      refine ⟨107566628225822370360802457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71711085483881580240534971 107566628225822370360802457)
      ·
        refine ⟨80674971169366777770601843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107566628225822370360802457 80674971169366777770601843)
        ·
          refine ⟨121012456754050166655902765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80674971169366777770601843 121012456754050166655902765)
          ·
            refine ⟨45379671282768812495963537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121012456754050166655902765 45379671282768812495963537)
            ·
              refine ⟨34034753462076609371972653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45379671282768812495963537 34034753462076609371972653)
              ·
                refine ⟨12763032548278728514489745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34034753462076609371972653 12763032548278728514489745)
                ·
                  refine ⟨9572274411209046385867309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12763032548278728514489745 9572274411209046385867309)
                  ·
                    refine ⟨3589602904203392394700241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9572274411209046385867309 3589602904203392394700241)
                    ·
                      refine ⟨2692202178152544296025181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3589602904203392394700241 2692202178152544296025181)
                      ·
                        rfl

theorem cell23_5243045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_5243045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243045 prefixEnd_5243045 := by exact prefixLift 5243045
  have htrace : WordTrace (prefixWord ++ tailWord_5243045) baseStart_5243045 baseEnd_5243045 := by
    simpa [prefixWord, tailWord_5243045, baseEnd_5243045] using wordTrace_append hprefix tailTrace_5243045
  have hstable : (prefixWord ++ tailWord_5243045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243045).length < 2 ^ (prefixWord ++ tailWord_5243045).sum := by decide
  have hdescent : baseEnd_5243045 < baseStart_5243045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243135 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 5, 3, 2]
def baseStart_5243135 : Nat := 118140960795 + 5243135 * 2 ^ 59
def prefixEnd_5243135 : Nat := 4983230072969 + 3 ^ 40 * 5243135 * 2
def baseEnd_5243135 : Nat := 2692248391411448943899767

theorem tailTrace_5243135 : CollatzResearch.WordTrace tailWord_5243135 prefixEnd_5243135 2692248391411448943899767 := by
  unfold tailWord_5243135
  simp only [CollatzResearch.WordTrace]
  refine ⟨191232843860024826012202859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127488562573349884008135239 191232843860024826012202859)
  ·
    refine ⟨286849265790037239018304289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191232843860024826012202859 286849265790037239018304289)
    ·
      refine ⟨215136949342527929263728217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286849265790037239018304289 215136949342527929263728217)
      ·
        refine ⟨161352712006895946947796163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215136949342527929263728217 161352712006895946947796163)
        ·
          refine ⟨242029068010343920421694245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161352712006895946947796163 242029068010343920421694245)
          ·
            refine ⟨45380450251939485079067671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 242029068010343920421694245 45380450251939485079067671)
            ·
              refine ⟨68070675377909227618601507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45380450251939485079067671 68070675377909227618601507)
              ·
                refine ⟨102106013066863841427902261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68070675377909227618601507 102106013066863841427902261)
                ·
                  refine ⟨9572438725018485133865837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102106013066863841427902261 9572438725018485133865837)
                  ·
                    refine ⟨3589664521881931925199689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9572438725018485133865837 3589664521881931925199689)
                    ·
                      refine ⟨2692248391411448943899767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3589664521881931925199689 2692248391411448943899767)
                      ·
                        rfl

theorem cell23_5243135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 3, 2].length) (baseStart_5243135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243135 prefixEnd_5243135 := by exact prefixLift 5243135
  have htrace : WordTrace (prefixWord ++ tailWord_5243135) baseStart_5243135 baseEnd_5243135 := by
    simpa [prefixWord, tailWord_5243135, baseEnd_5243135] using wordTrace_append hprefix tailTrace_5243135
  have hstable : (prefixWord ++ tailWord_5243135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243135).length < 2 ^ (prefixWord ++ tailWord_5243135).sum := by decide
  have hdescent : baseEnd_5243135 < baseStart_5243135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243148 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_5243148 : Nat := 118140960795 + 5243148 * 2 ^ 59
def prefixEnd_5243148 : Nat := 4983230072969 + 3 ^ 40 * 5243148 * 2
def baseEnd_5243148 : Nat := 2692255066659957393037207

theorem tailTrace_5243148 : CollatzResearch.WordTrace tailWord_5243148 prefixEnd_5243148 2692255066659957393037207 := by
  unfold tailWord_5243148
  simp only [CollatzResearch.WordTrace]
  refine ⟨95616659004488864616213049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127488878672651819488284065 95616659004488864616213049)
  ·
    refine ⟨71712494253366648462159787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95616659004488864616213049 71712494253366648462159787)
    ·
      refine ⟨107568741380049972693239681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71712494253366648462159787 107568741380049972693239681)
      ·
        refine ⟨80676556035037479519929761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107568741380049972693239681 80676556035037479519929761)
        ·
          refine ⟨60507417026278109639947321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80676556035037479519929761 60507417026278109639947321)
          ·
            refine ⟨45380562769708582229960491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60507417026278109639947321 45380562769708582229960491)
            ·
              refine ⟨68070844154562873344940737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45380562769708582229960491 68070844154562873344940737)
              ·
                refine ⟨51053133115922155008705553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68070844154562873344940737 51053133115922155008705553)
                ·
                  refine ⟨38289849836941616256529165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51053133115922155008705553 38289849836941616256529165)
                  ·
                    refine ⟨14358693688853106096198437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38289849836941616256529165 14358693688853106096198437)
                    ·
                      refine ⟨2692255066659957393037207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14358693688853106096198437 2692255066659957393037207)
                      ·
                        rfl

theorem cell23_5243148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_5243148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243148 prefixEnd_5243148 := by exact prefixLift 5243148
  have htrace : WordTrace (prefixWord ++ tailWord_5243148) baseStart_5243148 baseEnd_5243148 := by
    simpa [prefixWord, tailWord_5243148, baseEnd_5243148] using wordTrace_append hprefix tailTrace_5243148
  have hstable : (prefixWord ++ tailWord_5243148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243148).length < 2 ^ (prefixWord ++ tailWord_5243148).sum := by decide
  have hdescent : baseEnd_5243148 < baseStart_5243148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243169 : List Nat := [1, 2, 3, 2, 1, 1, 6, 1, 1, 3, 2]
def baseStart_5243169 : Nat := 118140960795 + 5243169 * 2 ^ 59
def prefixEnd_5243169 : Nat := 4983230072969 + 3 ^ 40 * 5243169 * 2
def baseEnd_5243169 : Nat := 2692265849753701810874611

theorem tailTrace_5243169 : CollatzResearch.WordTrace tailWord_5243169 prefixEnd_5243169 2692265849753701810874611 := by
  unfold tailWord_5243169
  simp only [CollatzResearch.WordTrace]
  refine ⟨191234083941901649818940561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127489389294601099879293707 191234083941901649818940561)
  ·
    refine ⟨143425562956426237364205421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191234083941901649818940561 143425562956426237364205421)
    ·
      refine ⟨53784586108659839011577033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143425562956426237364205421 53784586108659839011577033)
      ·
        refine ⟨40338439581494879258682775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53784586108659839011577033 40338439581494879258682775)
        ·
          refine ⟨60507659372242318888024163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40338439581494879258682775 60507659372242318888024163)
          ·
            refine ⟨90761489058363478332036245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60507659372242318888024163 90761489058363478332036245)
            ·
              refine ⟨4254444799610788046814199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90761489058363478332036245 4254444799610788046814199)
              ·
                refine ⟨6381667199416182070221299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4254444799610788046814199 6381667199416182070221299)
                ·
                  refine ⟨9572500799124273105331949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6381667199416182070221299 9572500799124273105331949)
                  ·
                    refine ⟨3589687799671602414499481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9572500799124273105331949 3589687799671602414499481)
                    ·
                      refine ⟨2692265849753701810874611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3589687799671602414499481 2692265849753701810874611)
                      ·
                        rfl

theorem cell23_5243169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_5243169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243169 prefixEnd_5243169 := by exact prefixLift 5243169
  have htrace : WordTrace (prefixWord ++ tailWord_5243169) baseStart_5243169 baseEnd_5243169 := by
    simpa [prefixWord, tailWord_5243169, baseEnd_5243169] using wordTrace_append hprefix tailTrace_5243169
  have hstable : (prefixWord ++ tailWord_5243169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243169).length < 2 ^ (prefixWord ++ tailWord_5243169).sum := by decide
  have hdescent : baseEnd_5243169 < baseStart_5243169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243176 : List Nat := [2, 1, 5, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_5243176 : Nat := 118140960795 + 5243176 * 2 ^ 59
def prefixEnd_5243176 : Nat := 4983230072969 + 3 ^ 40 * 5243176 * 2
def baseEnd_5243176 : Nat := 2692269444118283283487079

theorem tailTrace_5243176 : CollatzResearch.WordTrace tailWord_5243176 prefixEnd_5243176 2692269444118283283487079 := by
  unfold tailWord_5243176
  simp only [CollatzResearch.WordTrace]
  refine ⟨95617169626438145007222691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127489559501917526676296921 95617169626438145007222691)
  ·
    refine ⟨143425754439657217510834037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95617169626438145007222691 143425754439657217510834037)
    ·
      refine ⟨13446164478717864141640691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143425754439657217510834037 13446164478717864141640691)
      ·
        refine ⟨20169246718076796212461037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13446164478717864141640691 20169246718076796212461037)
        ·
          refine ⟨7563467519278798579672889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20169246718076796212461037 7563467519278798579672889)
          ·
            refine ⟨5672600639459098934754667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7563467519278798579672889 5672600639459098934754667)
            ·
              refine ⟨8508900959188648402132001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5672600639459098934754667 8508900959188648402132001)
              ·
                refine ⟨6381675719391486301599001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8508900959188648402132001 6381675719391486301599001)
                ·
                  refine ⟨4786256789543614726199251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6381675719391486301599001 4786256789543614726199251)
                  ·
                    refine ⟨7179385184315422089298877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4786256789543614726199251 7179385184315422089298877)
                    ·
                      refine ⟨2692269444118283283487079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7179385184315422089298877 2692269444118283283487079)
                      ·
                        rfl

theorem cell23_5243176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_5243176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243176 prefixEnd_5243176 := by exact prefixLift 5243176
  have htrace : WordTrace (prefixWord ++ tailWord_5243176) baseStart_5243176 baseEnd_5243176 := by
    simpa [prefixWord, tailWord_5243176, baseEnd_5243176] using wordTrace_append hprefix tailTrace_5243176
  have hstable : (prefixWord ++ tailWord_5243176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243176).length < 2 ^ (prefixWord ++ tailWord_5243176).sum := by decide
  have hdescent : baseEnd_5243176 < baseStart_5243176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243225 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 1, 7, 2]
def baseStart_5243225 : Nat := 118140960795 + 5243225 * 2 ^ 59
def prefixEnd_5243225 : Nat := 4983230072969 + 3 ^ 40 * 5243225 * 2
def baseEnd_5243225 : Nat := 2692294604670353591774353

theorem tailTrace_5243225 : CollatzResearch.WordTrace tailWord_5243225 prefixEnd_5243225 2692294604670353591774353 := by
  unfold tailWord_5243225
  simp only [CollatzResearch.WordTrace]
  refine ⟨191236126429698771382979129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127490750953132514255319419 191236126429698771382979129)
  ·
    refine ⟨143427094822274078537234347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191236126429698771382979129 143427094822274078537234347)
    ·
      refine ⟨215140642233411117805851521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143427094822274078537234347 215140642233411117805851521)
      ·
        refine ⟨161355481675058338354388641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215140642233411117805851521 161355481675058338354388641)
        ·
          refine ⟨121016611256293753765791481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161355481675058338354388641 121016611256293753765791481)
          ·
            refine ⟨90762458442220315324343611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121016611256293753765791481 90762458442220315324343611)
            ·
              refine ⟨136143687663330472986515417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90762458442220315324343611 136143687663330472986515417)
              ·
                refine ⟨102107765747497854739886563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136143687663330472986515417 102107765747497854739886563)
                ·
                  refine ⟨153161648621246782109829845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102107765747497854739886563 153161648621246782109829845)
                  ·
                    refine ⟨3589726139560471455699137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 153161648621246782109829845 3589726139560471455699137)
                    ·
                      refine ⟨2692294604670353591774353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3589726139560471455699137 2692294604670353591774353)
                      ·
                        rfl

theorem cell23_5243225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 7, 2].length) (baseStart_5243225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243225 prefixEnd_5243225 := by exact prefixLift 5243225
  have htrace : WordTrace (prefixWord ++ tailWord_5243225) baseStart_5243225 baseEnd_5243225 := by
    simpa [prefixWord, tailWord_5243225, baseEnd_5243225] using wordTrace_append hprefix tailTrace_5243225
  have hstable : (prefixWord ++ tailWord_5243225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243225).length < 2 ^ (prefixWord ++ tailWord_5243225).sum := by decide
  have hdescent : baseEnd_5243225 < baseStart_5243225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243235 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 2, 5]
def baseStart_5243235 : Nat := 118140960795 + 5243235 * 2 ^ 59
def prefixEnd_5243235 : Nat := 4983230072969 + 3 ^ 40 * 5243235 * 2
def baseEnd_5243235 : Nat := 897433246492299517549769

theorem tailTrace_5243235 : CollatzResearch.WordTrace tailWord_5243235 prefixEnd_5243235 897433246492299517549769 := by
  unfold tailWord_5243235
  simp only [CollatzResearch.WordTrace]
  refine ⟨191236491159662543090843159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127490994106441695393895439 191236491159662543090843159)
  ·
    refine ⟨286854736739493814636264739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191236491159662543090843159 286854736739493814636264739)
    ·
      refine ⟨430282105109240721954397109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286854736739493814636264739 430282105109240721954397109)
      ·
        refine ⟨40338947353991317683224729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 430282105109240721954397109 40338947353991317683224729)
        ·
          refine ⟨30254210515493488262418547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40338947353991317683224729 30254210515493488262418547)
          ·
            refine ⟨45381315773240232393627821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30254210515493488262418547 45381315773240232393627821)
            ·
              refine ⟨17017993414965087147610433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45381315773240232393627821 17017993414965087147610433)
              ·
                refine ⟨12763495061223815360707825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17017993414965087147610433 12763495061223815360707825)
                ·
                  refine ⟨9572621295917861520530869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12763495061223815360707825 9572621295917861520530869)
                  ·
                    refine ⟨897433246492299517549769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9572621295917861520530869 897433246492299517549769)
                    ·
                      rfl

theorem cell23_5243235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 5].length) (baseStart_5243235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243235 prefixEnd_5243235 := by exact prefixLift 5243235
  have htrace : WordTrace (prefixWord ++ tailWord_5243235) baseStart_5243235 baseEnd_5243235 := by
    simpa [prefixWord, tailWord_5243235, baseEnd_5243235] using wordTrace_append hprefix tailTrace_5243235
  have hstable : (prefixWord ++ tailWord_5243235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243235).length < 2 ^ (prefixWord ++ tailWord_5243235).sum := by decide
  have hdescent : baseEnd_5243235 < baseStart_5243235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243239 : List Nat := [1, 1, 5, 1, 3, 2, 3, 2, 5]
def baseStart_5243239 : Nat := 118140960795 + 5243239 * 2 ^ 59
def prefixEnd_5243239 : Nat := 4983230072969 + 3 ^ 40 * 5243239 * 2
def baseEnd_5243239 : Nat := 299144643711057392999921

theorem tailTrace_5243239 : CollatzResearch.WordTrace tailWord_5243239 prefixEnd_5243239 299144643711057392999921 := by
  unfold tailWord_5243239
  simp only [CollatzResearch.WordTrace]
  refine ⟨191236637051648051773988771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127491091367765367849325847 191236637051648051773988771)
  ·
    refine ⟨286854955577472077660983157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191236637051648051773988771 286854955577472077660983157)
    ·
      refine ⟨26892652085388007280717171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 286854955577472077660983157 26892652085388007280717171)
      ·
        refine ⟨40338978128082010921075757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26892652085388007280717171 40338978128082010921075757)
        ·
          refine ⟨15127116798030754095403409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40338978128082010921075757 15127116798030754095403409)
          ·
            refine ⟨11345337598523065571552557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15127116798030754095403409 11345337598523065571552557)
            ·
              refine ⟨4254501599446149589332209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11345337598523065571552557 4254501599446149589332209)
              ·
                refine ⟨3190876199584612191999157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4254501599446149589332209 3190876199584612191999157)
                ·
                  refine ⟨299144643711057392999921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3190876199584612191999157 299144643711057392999921)
                  ·
                    rfl

theorem cell23_5243239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 5].length) (baseStart_5243239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243239 prefixEnd_5243239 := by exact prefixLift 5243239
  have htrace : WordTrace (prefixWord ++ tailWord_5243239) baseStart_5243239 baseEnd_5243239 := by
    simpa [prefixWord, tailWord_5243239, baseEnd_5243239] using wordTrace_append hprefix tailTrace_5243239
  have hstable : (prefixWord ++ tailWord_5243239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243239).length < 2 ^ (prefixWord ++ tailWord_5243239).sum := by decide
  have hdescent : baseEnd_5243239 < baseStart_5243239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243245 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_5243245 : Nat := 118140960795 + 5243245 * 2 ^ 59
def prefixEnd_5243245 : Nat := 4983230072969 + 3 ^ 40 * 5243245 * 2
def baseEnd_5243245 : Nat := 2692304874283443513524261

theorem tailTrace_5243245 : CollatzResearch.WordTrace tailWord_5243245 prefixEnd_5243245 2692304874283443513524261 := by
  unfold tailWord_5243245
  simp only [CollatzResearch.WordTrace]
  refine ⟨191236855889626314798707189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127491237259750876532471459 191236855889626314798707189)
  ·
    refine ⟨17928455239652467012378799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191236855889626314798707189 17928455239652467012378799)
    ·
      refine ⟨26892682859478700518568199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17928455239652467012378799 26892682859478700518568199)
      ·
        refine ⟨40339024289218050777852299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26892682859478700518568199 40339024289218050777852299)
        ·
          refine ⟨60508536433827076166778449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40339024289218050777852299 60508536433827076166778449)
          ·
            refine ⟨45381402325370307125083837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60508536433827076166778449 45381402325370307125083837)
            ·
              refine ⟨17018025872013865171906439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45381402325370307125083837 17018025872013865171906439)
              ·
                refine ⟨25527038808020797757859659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17018025872013865171906439 25527038808020797757859659)
                ·
                  refine ⟨38290558212031196636789489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25527038808020797757859659 38290558212031196636789489)
                  ·
                    refine ⟨28717918659023397477592117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38290558212031196636789489 28717918659023397477592117)
                    ·
                      refine ⟨2692304874283443513524261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28717918659023397477592117 2692304874283443513524261)
                      ·
                        rfl

theorem cell23_5243245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_5243245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243245 prefixEnd_5243245 := by exact prefixLift 5243245
  have htrace : WordTrace (prefixWord ++ tailWord_5243245) baseStart_5243245 baseEnd_5243245 := by
    simpa [prefixWord, tailWord_5243245, baseEnd_5243245] using wordTrace_append hprefix tailTrace_5243245
  have hstable : (prefixWord ++ tailWord_5243245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243245).length < 2 ^ (prefixWord ++ tailWord_5243245).sum := by decide
  have hdescent : baseEnd_5243245 < baseStart_5243245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243272 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_5243272 : Nat := 118140960795 + 5243272 * 2 ^ 59
def prefixEnd_5243272 : Nat := 4983230072969 + 3 ^ 40 * 5243272 * 2
def baseEnd_5243272 : Nat := 2692318738261114907886637

theorem tailTrace_5243272 : CollatzResearch.WordTrace tailWord_5243272 prefixEnd_5243272 2692318738261114907886637 := by
  unfold tailWord_5243272
  simp only [CollatzResearch.WordTrace]
  refine ⟨95618920330264249204970035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127491893773685665606626713 95618920330264249204970035)
  ·
    refine ⟨143428380495396373807455053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95618920330264249204970035 143428380495396373807455053)
    ·
      refine ⟨53785642685773640177795645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143428380495396373807455053 53785642685773640177795645)
      ·
        refine ⟨20169616007165115066673367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53785642685773640177795645 20169616007165115066673367)
        ·
          refine ⟨30254424010747672600010051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20169616007165115066673367 30254424010747672600010051)
          ·
            refine ⟨45381636016121508900015077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30254424010747672600010051 45381636016121508900015077)
            ·
              refine ⟨8509056753022782918752827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45381636016121508900015077 8509056753022782918752827)
              ·
                refine ⟨12763585129534174378129241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8509056753022782918752827 12763585129534174378129241)
                ·
                  refine ⟨9572688847150630783596931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12763585129534174378129241 9572688847150630783596931)
                  ·
                    refine ⟨14359033270725946175395397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9572688847150630783596931 14359033270725946175395397)
                    ·
                      refine ⟨2692318738261114907886637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14359033270725946175395397 2692318738261114907886637)
                      ·
                        rfl

theorem cell23_5243272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_5243272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243272 prefixEnd_5243272 := by exact prefixLift 5243272
  have htrace : WordTrace (prefixWord ++ tailWord_5243272) baseStart_5243272 baseEnd_5243272 := by
    simpa [prefixWord, tailWord_5243272, baseEnd_5243272] using wordTrace_append hprefix tailTrace_5243272
  have hstable : (prefixWord ++ tailWord_5243272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243272).length < 2 ^ (prefixWord ++ tailWord_5243272).sum := by decide
  have hdescent : baseEnd_5243272 < baseStart_5243272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243299 : List Nat := [1, 1, 1, 4, 1, 5, 1, 4, 1, 4]
def baseStart_5243299 : Nat := 118140960795 + 5243299 * 2 ^ 59
def prefixEnd_5243299 : Nat := 4983230072969 + 3 ^ 40 * 5243299 * 2
def baseEnd_5243299 : Nat := 897444200746262100749671

theorem tailTrace_5243299 : CollatzResearch.WordTrace tailWord_5243299 prefixEnd_5243299 897444200746262100749671 := by
  unfold tailWord_5243299
  simp only [CollatzResearch.WordTrace]
  refine ⟨191238825431430682021172951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127492550287620454680781967 191238825431430682021172951)
  ·
    refine ⟨286858238147146023031759427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191238825431430682021172951 286858238147146023031759427)
    ·
      refine ⟨430287357220719034547639141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286858238147146023031759427 430287357220719034547639141)
      ·
        refine ⟨80678879478884818977682339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 430287357220719034547639141 80678879478884818977682339)
        ·
          refine ⟨121018319218327228466523509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80678879478884818977682339 121018319218327228466523509)
          ·
            refine ⟨11345467426718177668736579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121018319218327228466523509 11345467426718177668736579)
            ·
              refine ⟨17018201140077266503104869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11345467426718177668736579 17018201140077266503104869)
              ·
                refine ⟨3190912713764487469332163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17018201140077266503104869 3190912713764487469332163)
                ·
                  refine ⟨4786369070646731203998245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3190912713764487469332163 4786369070646731203998245)
                  ·
                    refine ⟨897444200746262100749671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4786369070646731203998245 897444200746262100749671)
                    ·
                      rfl

theorem cell23_5243299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 1, 4].length) (baseStart_5243299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243299 prefixEnd_5243299 := by exact prefixLift 5243299
  have htrace : WordTrace (prefixWord ++ tailWord_5243299) baseStart_5243299 baseEnd_5243299 := by
    simpa [prefixWord, tailWord_5243299, baseEnd_5243299] using wordTrace_append hprefix tailTrace_5243299
  have hstable : (prefixWord ++ tailWord_5243299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243299).length < 2 ^ (prefixWord ++ tailWord_5243299).sum := by decide
  have hdescent : baseEnd_5243299 < baseStart_5243299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243346 : List Nat := [3, 2, 2, 4, 1, 2, 1, 2, 6]
def baseStart_5243346 : Nat := 118140960795 + 5243346 * 2 ^ 59
def prefixEnd_5243346 : Nat := 4983230072969 + 3 ^ 40 * 5243346 * 2
def baseEnd_5243346 : Nat := 299150748425505290929033

theorem tailTrace_5243346 : CollatzResearch.WordTrace tailWord_5243346 prefixEnd_5243346 299150748425505290929033 := by
  unfold tailWord_5243346
  simp only [CollatzResearch.WordTrace]
  refine ⟨47810134915565102262033473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127493693108173606032089261 47810134915565102262033473)
  ·
    refine ⟨35857601186673826696525105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47810134915565102262033473 35857601186673826696525105)
    ·
      refine ⟨26893200890005370022393829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35857601186673826696525105 26893200890005370022393829)
      ·
        refine ⟨5042475166876006879198843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26893200890005370022393829 5042475166876006879198843)
        ·
          refine ⟨7563712750314010318798265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5042475166876006879198843 7563712750314010318798265)
          ·
            refine ⟨5672784562735507739098699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7563712750314010318798265 5672784562735507739098699)
            ·
              refine ⟨8509176844103261608648049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5672784562735507739098699 8509176844103261608648049)
              ·
                refine ⟨6381882633077446206486037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8509176844103261608648049 6381882633077446206486037)
                ·
                  refine ⟨299150748425505290929033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6381882633077446206486037 299150748425505290929033)
                  ·
                    rfl

theorem cell23_5243346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_5243346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243346 prefixEnd_5243346 := by exact prefixLift 5243346
  have htrace : WordTrace (prefixWord ++ tailWord_5243346) baseStart_5243346 baseEnd_5243346 := by
    simpa [prefixWord, tailWord_5243346, baseEnd_5243346] using wordTrace_append hprefix tailTrace_5243346
  have hstable : (prefixWord ++ tailWord_5243346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243346).length < 2 ^ (prefixWord ++ tailWord_5243346).sum := by decide
  have hdescent : baseEnd_5243346 < baseStart_5243346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243379 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 3, 2, 2]
def baseStart_5243379 : Nat := 118140960795 + 5243379 * 2 ^ 59
def prefixEnd_5243379 : Nat := 4983230072969 + 3 ^ 40 * 5243379 * 2
def baseEnd_5243379 : Nat := 2692373680691145989248645

theorem tailTrace_5243379 : CollatzResearch.WordTrace tailWord_5243379 prefixEnd_5243379 2692373680691145989248645 := by
  unfold tailWord_5243379
  simp only [CollatzResearch.WordTrace]
  refine ⟨191241743271140855684085191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127494495514093903789390127 191241743271140855684085191)
  ·
    refine ⟨286862614906711283526127787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191241743271140855684085191 286862614906711283526127787)
    ·
      refine ⟨430293922360066925289191681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286862614906711283526127787 430293922360066925289191681)
      ·
        refine ⟨322720441770050193966893761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430293922360066925289191681 322720441770050193966893761)
        ·
          refine ⟨242040331327537645475170321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322720441770050193966893761 242040331327537645475170321)
          ·
            refine ⟨181530248495653234106377741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242040331327537645475170321 181530248495653234106377741)
            ·
              refine ⟨68073843185869962789891653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181530248495653234106377741 68073843185869962789891653)
              ·
                refine ⟨12763845597350618023104685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68073843185869962789891653 12763845597350618023104685)
                ·
                  refine ⟨4786442099006481758664257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12763845597350618023104685 4786442099006481758664257)
                  ·
                    refine ⟨3589831574254861318998193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4786442099006481758664257 3589831574254861318998193)
                    ·
                      refine ⟨2692373680691145989248645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3589831574254861318998193 2692373680691145989248645)
                      ·
                        rfl

theorem cell23_5243379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 2, 2].length) (baseStart_5243379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243379 prefixEnd_5243379 := by exact prefixLift 5243379
  have htrace : WordTrace (prefixWord ++ tailWord_5243379) baseStart_5243379 baseEnd_5243379 := by
    simpa [prefixWord, tailWord_5243379, baseEnd_5243379] using wordTrace_append hprefix tailTrace_5243379
  have hstable : (prefixWord ++ tailWord_5243379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243379).length < 2 ^ (prefixWord ++ tailWord_5243379).sum := by decide
  have hdescent : baseEnd_5243379 < baseStart_5243379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243382 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_5243382 : Nat := 118140960795 + 5243382 * 2 ^ 59
def prefixEnd_5243382 : Nat := 4983230072969 + 3 ^ 40 * 5243382 * 2
def baseEnd_5243382 : Nat := 2692375221133109477511131

theorem tailTrace_5243382 : CollatzResearch.WordTrace tailWord_5243382 prefixEnd_5243382 2692375221133109477511131 := by
  unfold tailWord_5243382
  simp only [CollatzResearch.WordTrace]
  refine ⟨11952615793133124199777775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127494568460086658130962933 11952615793133124199777775)
  ·
    refine ⟨17928923689699686299666663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11952615793133124199777775 17928923689699686299666663)
    ·
      refine ⟨26893385534549529449499995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17928923689699686299666663 26893385534549529449499995)
      ·
        refine ⟨40340078301824294174249993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26893385534549529449499995 40340078301824294174249993)
        ·
          refine ⟨30255058726368220630687495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40340078301824294174249993 30255058726368220630687495)
          ·
            refine ⟨45382588089552330946031243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30255058726368220630687495 45382588089552330946031243)
            ·
              refine ⟨68073882134328496419046865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45382588089552330946031243 68073882134328496419046865)
              ·
                refine ⟨51055411600746372314285149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68073882134328496419046865 51055411600746372314285149)
                ·
                  refine ⟨19145779350279889617856931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51055411600746372314285149 19145779350279889617856931)
                  ·
                    refine ⟨28718669025419834426785397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19145779350279889617856931 28718669025419834426785397)
                    ·
                      refine ⟨2692375221133109477511131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28718669025419834426785397 2692375221133109477511131)
                      ·
                        rfl

theorem cell23_5243382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_5243382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243382 prefixEnd_5243382 := by exact prefixLift 5243382
  have htrace : WordTrace (prefixWord ++ tailWord_5243382) baseStart_5243382 baseEnd_5243382 := by
    simpa [prefixWord, tailWord_5243382, baseEnd_5243382] using wordTrace_append hprefix tailTrace_5243382
  have hstable : (prefixWord ++ tailWord_5243382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243382).length < 2 ^ (prefixWord ++ tailWord_5243382).sum := by decide
  have hdescent : baseEnd_5243382 < baseStart_5243382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243399 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_5243399 : Nat := 118140960795 + 5243399 * 2 ^ 59
def prefixEnd_5243399 : Nat := 4983230072969 + 3 ^ 40 * 5243399 * 2
def baseEnd_5243399 : Nat := 2692383950304235910998553

theorem tailTrace_5243399 : CollatzResearch.WordTrace tailWord_5243399 prefixEnd_5243399 2692383950304235910998553 := by
  unfold tailWord_5243399
  simp only [CollatzResearch.WordTrace]
  refine ⟨191242472731068399099813251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127494981820712266066542167 191242472731068399099813251)
  ·
    refine ⟨286863709096602598649719877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191242472731068399099813251 286863709096602598649719877)
    ·
      refine ⟨53786945455612987246822477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286863709096602598649719877 53786945455612987246822477)
      ·
        refine ⟨20170104545854870217558429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53786945455612987246822477 20170104545854870217558429)
        ·
          refine ⟨7563789204695576331584411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20170104545854870217558429 7563789204695576331584411)
          ·
            refine ⟨11345683807043364497376617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7563789204695576331584411 11345683807043364497376617)
            ·
              refine ⟨8509262855282523373032463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11345683807043364497376617 8509262855282523373032463)
              ·
                refine ⟨12763894282923785059548695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8509262855282523373032463 12763894282923785059548695)
                ·
                  refine ⟨19145841424385677589323043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12763894282923785059548695 19145841424385677589323043)
                  ·
                    refine ⟨28718762136578516383984565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19145841424385677589323043 28718762136578516383984565)
                    ·
                      refine ⟨2692383950304235910998553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28718762136578516383984565 2692383950304235910998553)
                      ·
                        rfl

theorem cell23_5243399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_5243399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243399 prefixEnd_5243399 := by exact prefixLift 5243399
  have htrace : WordTrace (prefixWord ++ tailWord_5243399) baseStart_5243399 baseEnd_5243399 := by
    simpa [prefixWord, tailWord_5243399, baseEnd_5243399] using wordTrace_append hprefix tailTrace_5243399
  have hstable : (prefixWord ++ tailWord_5243399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243399).length < 2 ^ (prefixWord ++ tailWord_5243399).sum := by decide
  have hdescent : baseEnd_5243399 < baseStart_5243399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243446 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_5243446 : Nat := 118140960795 + 5243446 * 2 ^ 59
def prefixEnd_5243446 : Nat := 4983230072969 + 3 ^ 40 * 5243446 * 2
def baseEnd_5243446 : Nat := 2692408083894997227110837

theorem tailTrace_5243446 : CollatzResearch.WordTrace tailWord_5243446 prefixEnd_5243446 2692408083894997227110837 := by
  unfold tailWord_5243446
  simp only [CollatzResearch.WordTrace]
  refine ⟨11952761685118632882923387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127496124641265417417849461 11952761685118632882923387)
  ·
    refine ⟨17929142527677949324385081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11952761685118632882923387 17929142527677949324385081)
    ·
      refine ⟨13446856895758461993288811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17929142527677949324385081 13446856895758461993288811)
      ·
        refine ⟨20170285343637692989933217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13446856895758461993288811 20170285343637692989933217)
        ·
          refine ⟨15127714007728269742449913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20170285343637692989933217 15127714007728269742449913)
          ·
            refine ⟨11345785505796202306837435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15127714007728269742449913 11345785505796202306837435)
            ·
              refine ⟨17018678258694303460256153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11345785505796202306837435 17018678258694303460256153)
              ·
                refine ⟨12764008694020727595192115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17018678258694303460256153 12764008694020727595192115)
                ·
                  refine ⟨19146013041031091392788173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12764008694020727595192115 19146013041031091392788173)
                  ·
                    refine ⟨7179754890386659272295565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19146013041031091392788173 7179754890386659272295565)
                    ·
                      refine ⟨2692408083894997227110837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7179754890386659272295565 2692408083894997227110837)
                      ·
                        rfl

theorem cell23_5243446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_5243446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243446 prefixEnd_5243446 := by exact prefixLift 5243446
  have htrace : WordTrace (prefixWord ++ tailWord_5243446) baseStart_5243446 baseEnd_5243446 := by
    simpa [prefixWord, tailWord_5243446, baseEnd_5243446] using wordTrace_append hprefix tailTrace_5243446
  have hstable : (prefixWord ++ tailWord_5243446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243446).length < 2 ^ (prefixWord ++ tailWord_5243446).sum := by decide
  have hdescent : baseEnd_5243446 < baseStart_5243446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243465 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 6]
def baseStart_5243465 : Nat := 118140960795 + 5243465 * 2 ^ 59
def prefixEnd_5243465 : Nat := 4983230072969 + 3 ^ 40 * 5243465 * 2
def baseEnd_5243465 : Nat := 2692417840027432652773249

theorem tailTrace_5243465 : CollatzResearch.WordTrace tailWord_5243465 prefixEnd_5243465 2692417840027432652773249 := by
  unfold tailWord_5243465
  simp only [CollatzResearch.WordTrace]
  refine ⟨191244879948829292371715849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127496586632552861581143899 191244879948829292371715849)
  ·
    refine ⟨143433659961621969278786887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191244879948829292371715849 143433659961621969278786887)
    ·
      refine ⟨215150489942432953918180331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143433659961621969278786887 215150489942432953918180331)
      ·
        refine ⟨322725734913649430877270497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215150489942432953918180331 322725734913649430877270497)
        ·
          refine ⟨242044301185237073157952873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322725734913649430877270497 242044301185237073157952873)
          ·
            refine ⟨181533225888927804868464655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242044301185237073157952873 181533225888927804868464655)
            ·
              refine ⟨272299838833391707302696983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181533225888927804868464655 272299838833391707302696983)
              ·
                refine ⟨408449758250087560954045475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272299838833391707302696983 408449758250087560954045475)
                ·
                  refine ⟨612674637375131341431068213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408449758250087560954045475 612674637375131341431068213)
                  ·
                    refine ⟨57438247253918563259162645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 612674637375131341431068213 57438247253918563259162645)
                    ·
                      refine ⟨2692417840027432652773249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57438247253918563259162645 2692417840027432652773249)
                      ·
                        rfl

theorem cell23_5243465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_5243465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243465 prefixEnd_5243465 := by exact prefixLift 5243465
  have htrace : WordTrace (prefixWord ++ tailWord_5243465) baseStart_5243465 baseEnd_5243465 := by
    simpa [prefixWord, tailWord_5243465, baseEnd_5243465] using wordTrace_append hprefix tailTrace_5243465
  have hstable : (prefixWord ++ tailWord_5243465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243465).length < 2 ^ (prefixWord ++ tailWord_5243465).sum := by decide
  have hdescent : baseEnd_5243465 < baseStart_5243465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243469 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_5243469 : Nat := 118140960795 + 5243469 * 2 ^ 59
def prefixEnd_5243469 : Nat := 4983230072969 + 3 ^ 40 * 5243469 * 2
def baseEnd_5243469 : Nat := 2692419893950050637123231

theorem tailTrace_5243469 : CollatzResearch.WordTrace tailWord_5243469 prefixEnd_5243469 2692419893950050637123231 := by
  unfold tailWord_5243469
  simp only [CollatzResearch.WordTrace]
  refine ⟨191245025840814801054861461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127496683893876534036574307 191245025840814801054861461)
  ·
    refine ⟨8964610586288193799446631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 191245025840814801054861461 8964610586288193799446631)
    ·
      refine ⟨13446915879432290699169947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8964610586288193799446631 13446915879432290699169947)
      ·
        refine ⟨20170373819148436048754921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13446915879432290699169947 20170373819148436048754921)
        ·
          refine ⟨15127780364361327036566191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20170373819148436048754921 15127780364361327036566191)
          ·
            refine ⟨22691670546541990554849287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15127780364361327036566191 22691670546541990554849287)
            ·
              refine ⟨34037505819812985832273931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22691670546541990554849287 34037505819812985832273931)
              ·
                refine ⟨51056258729719478748410897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34037505819812985832273931 51056258729719478748410897)
                ·
                  refine ⟨38292194047289609061308173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51056258729719478748410897 38292194047289609061308173)
                  ·
                    refine ⟨14359572767733603397990565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38292194047289609061308173 14359572767733603397990565)
                    ·
                      refine ⟨2692419893950050637123231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14359572767733603397990565 2692419893950050637123231)
                      ·
                        rfl

theorem cell23_5243469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_5243469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243469 prefixEnd_5243469 := by exact prefixLift 5243469
  have htrace : WordTrace (prefixWord ++ tailWord_5243469) baseStart_5243469 baseEnd_5243469 := by
    simpa [prefixWord, tailWord_5243469, baseEnd_5243469] using wordTrace_append hprefix tailTrace_5243469
  have hstable : (prefixWord ++ tailWord_5243469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243469).length < 2 ^ (prefixWord ++ tailWord_5243469).sum := by decide
  have hdescent : baseEnd_5243469 < baseStart_5243469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243492 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 7]
def baseStart_5243492 : Nat := 118140960795 + 5243492 * 2 ^ 59
def prefixEnd_5243492 : Nat := 4983230072969 + 3 ^ 40 * 5243492 * 2
def baseEnd_5243492 : Nat := 299159078222789338570625

theorem tailTrace_5243492 : CollatzResearch.WordTrace tailWord_5243492 prefixEnd_5243492 299159078222789338570625 := by
  unfold tailWord_5243492
  simp only [CollatzResearch.WordTrace]
  refine ⟨95622932359865737991474365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127497243146487650655299153 95622932359865737991474365)
  ·
    refine ⟨35858599634949651746802887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95622932359865737991474365 35858599634949651746802887)
    ·
      refine ⟨53787899452424477620204331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35858599634949651746802887 53787899452424477620204331)
      ·
        refine ⟨80681849178636716430306497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53787899452424477620204331 80681849178636716430306497)
        ·
          refine ⟨60511386883977537322729873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80681849178636716430306497 60511386883977537322729873)
          ·
            refine ⟨45383540162983152992047405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60511386883977537322729873 45383540162983152992047405)
            ·
              refine ⟨17018827561118682372017777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45383540162983152992047405 17018827561118682372017777)
              ·
                refine ⟨12764120670839011779013333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17018827561118682372017777 12764120670839011779013333)
                ·
                  refine ⟨299159078222789338570625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12764120670839011779013333 299159078222789338570625)
                  ·
                    rfl

theorem cell23_5243492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_5243492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243492 prefixEnd_5243492 := by exact prefixLift 5243492
  have htrace : WordTrace (prefixWord ++ tailWord_5243492) baseStart_5243492 baseEnd_5243492 := by
    simpa [prefixWord, tailWord_5243492, baseEnd_5243492] using wordTrace_append hprefix tailTrace_5243492
  have hstable : (prefixWord ++ tailWord_5243492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243492).length < 2 ^ (prefixWord ++ tailWord_5243492).sum := by decide
  have hdescent : baseEnd_5243492 < baseStart_5243492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243646 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_5243646 : Nat := 118140960795 + 5243646 * 2 ^ 59
def prefixEnd_5243646 : Nat := 4983230072969 + 3 ^ 40 * 5243646 * 2
def baseEnd_5243646 : Nat := 897503593341965481536639

theorem tailTrace_5243646 : CollatzResearch.WordTrace tailWord_5243646 prefixEnd_5243646 897503593341965481536639 := by
  unfold tailWord_5243646
  simp only [CollatzResearch.WordTrace]
  refine ⟨23906435195146695035506849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127500987707449040189369861 23906435195146695035506849)
  ·
    refine ⟨17929826396360021276630137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23906435195146695035506849 17929826396360021276630137)
    ·
      refine ⟨13447369797270015957472603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17929826396360021276630137 13447369797270015957472603)
      ·
        refine ⟨20171054695905023936208905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13447369797270015957472603 20171054695905023936208905)
        ·
          refine ⟨15128291021928767952156679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20171054695905023936208905 15128291021928767952156679)
          ·
            refine ⟨22692436532893151928235019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15128291021928767952156679 22692436532893151928235019)
            ·
              refine ⟨34038654799339727892352529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22692436532893151928235019 34038654799339727892352529)
              ·
                refine ⟨25528991099504795919264397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34038654799339727892352529 25528991099504795919264397)
                ·
                  refine ⟨9573371662314298469724149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25528991099504795919264397 9573371662314298469724149)
                  ·
                    refine ⟨897503593341965481536639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9573371662314298469724149 897503593341965481536639)
                    ·
                      rfl

theorem cell23_5243646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_5243646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243646 prefixEnd_5243646 := by exact prefixLift 5243646
  have htrace : WordTrace (prefixWord ++ tailWord_5243646) baseStart_5243646 baseEnd_5243646 := by
    simpa [prefixWord, tailWord_5243646, baseEnd_5243646] using wordTrace_append hprefix tailTrace_5243646
  have hstable : (prefixWord ++ tailWord_5243646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243646).length < 2 ^ (prefixWord ++ tailWord_5243646).sum := by decide
  have hdescent : baseEnd_5243646 < baseStart_5243646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243659 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 6, 4]
def baseStart_5243659 : Nat := 118140960795 + 5243659 * 2 ^ 59
def prefixEnd_5243659 : Nat := 4983230072969 + 3 ^ 40 * 5243659 * 2
def baseEnd_5243659 : Nat := 897505818424801631249119

theorem tailTrace_5243659 : CollatzResearch.WordTrace tailWord_5243659 prefixEnd_5243659 897505818424801631249119 := by
  unfold tailWord_5243659
  simp only [CollatzResearch.WordTrace]
  refine ⟨191251955710126463504278031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127501303806750975669518687 191251955710126463504278031)
  ·
    refine ⟨286877933565189695256417047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191251955710126463504278031 286877933565189695256417047)
    ·
      refine ⟨430316900347784542884625571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286877933565189695256417047 430316900347784542884625571)
      ·
        refine ⟨645475350521676814326938357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430316900347784542884625571 645475350521676814326938357)
        ·
          refine ⟨60513314111407201343150471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 645475350521676814326938357 60513314111407201343150471)
          ·
            refine ⟨90769971167110802014725707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60513314111407201343150471 90769971167110802014725707)
            ·
              refine ⟨136154956750666203022088561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90769971167110802014725707 136154956750666203022088561)
              ·
                refine ⟨102116217562999652266566421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136154956750666203022088561 102116217562999652266566421)
                ·
                  refine ⟨4786697698265608699995301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102116217562999652266566421 4786697698265608699995301)
                  ·
                    refine ⟨897505818424801631249119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4786697698265608699995301 897505818424801631249119)
                    ·
                      rfl

theorem cell23_5243659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 4].length) (baseStart_5243659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243659 prefixEnd_5243659 := by exact prefixLift 5243659
  have htrace : WordTrace (prefixWord ++ tailWord_5243659) baseStart_5243659 baseEnd_5243659 := by
    simpa [prefixWord, tailWord_5243659, baseEnd_5243659] using wordTrace_append hprefix tailTrace_5243659
  have hstable : (prefixWord ++ tailWord_5243659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243659).length < 2 ^ (prefixWord ++ tailWord_5243659).sum := by decide
  have hdescent : baseEnd_5243659 < baseStart_5243659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243710 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_5243710 : Nat := 118140960795 + 5243710 * 2 ^ 59
def prefixEnd_5243710 : Nat := 4983230072969 + 3 ^ 40 * 5243710 * 2
def baseEnd_5243710 : Nat := 897514547595928064736541

theorem tailTrace_5243710 : CollatzResearch.WordTrace tailWord_5243710 prefixEnd_5243710 897514547595928064736541 := by
  unfold tailWord_5243710
  simp only [CollatzResearch.WordTrace]
  refine ⟨23906726979117712401798073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127502543888627799476256389 23906726979117712401798073)
  ·
    refine ⟨17930045234338284301348555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23906726979117712401798073 17930045234338284301348555)
    ·
      refine ⟨26895067851507426452022833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17930045234338284301348555 26895067851507426452022833)
      ·
        refine ⟨20171300888630569839017125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26895067851507426452022833 20171300888630569839017125)
        ·
          refine ⟨3782118916618231844815711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20171300888630569839017125 3782118916618231844815711)
          ·
            refine ⟨5673178374927347767223567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3782118916618231844815711 5673178374927347767223567)
            ·
              refine ⟨8509767562391021650835351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5673178374927347767223567 8509767562391021650835351)
              ·
                refine ⟨12764651343586532476253027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8509767562391021650835351 12764651343586532476253027)
                ·
                  refine ⟨19146977015379798714379541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12764651343586532476253027 19146977015379798714379541)
                  ·
                    refine ⟨897514547595928064736541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19146977015379798714379541 897514547595928064736541)
                    ·
                      rfl

theorem cell23_5243710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_5243710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243710 prefixEnd_5243710 := by exact prefixLift 5243710
  have htrace : WordTrace (prefixWord ++ tailWord_5243710) baseStart_5243710 baseEnd_5243710 := by
    simpa [prefixWord, tailWord_5243710, baseEnd_5243710] using wordTrace_append hprefix tailTrace_5243710
  have hstable : (prefixWord ++ tailWord_5243710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243710).length < 2 ^ (prefixWord ++ tailWord_5243710).sum := by decide
  have hdescent : baseEnd_5243710 < baseStart_5243710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243713 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5243713 : Nat := 118140960795 + 5243713 * 2 ^ 59
def prefixEnd_5243713 : Nat := 4983230072969 + 3 ^ 40 * 5243713 * 2
def baseEnd_5243713 : Nat := 2692545183229747682472109

theorem tailTrace_5243713 : CollatzResearch.WordTrace tailWord_5243713 prefixEnd_5243713 2692545183229747682472109 := by
  unfold tailWord_5243713
  simp only [CollatzResearch.WordTrace]
  refine ⟨191253925251930830726743793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127502616834620553817829195 191253925251930830726743793)
  ·
    refine ⟨143440443938948123045057845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191253925251930830726743793 143440443938948123045057845)
    ·
      refine ⟨13447541619276386535474173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143440443938948123045057845 13447541619276386535474173)
      ·
        refine ⟨5042828107228644950802815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13447541619276386535474173 5042828107228644950802815)
        ·
          refine ⟨7564242160842967426204223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5042828107228644950802815 7564242160842967426204223)
          ·
            refine ⟨11346363241264451139306335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7564242160842967426204223 11346363241264451139306335)
            ·
              refine ⟨17019544861896676708959503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11346363241264451139306335 17019544861896676708959503)
              ·
                refine ⟨25529317292845015063439255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17019544861896676708959503 25529317292845015063439255)
                ·
                  refine ⟨38293975939267522595158883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25529317292845015063439255 38293975939267522595158883)
                  ·
                    refine ⟨57440963908901283892738325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38293975939267522595158883 57440963908901283892738325)
                    ·
                      refine ⟨2692545183229747682472109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57440963908901283892738325 2692545183229747682472109)
                      ·
                        rfl

theorem cell23_5243713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5243713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243713 prefixEnd_5243713 := by exact prefixLift 5243713
  have htrace : WordTrace (prefixWord ++ tailWord_5243713) baseStart_5243713 baseEnd_5243713 := by
    simpa [prefixWord, tailWord_5243713, baseEnd_5243713] using wordTrace_append hprefix tailTrace_5243713
  have hstable : (prefixWord ++ tailWord_5243713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243713).length < 2 ^ (prefixWord ++ tailWord_5243713).sum := by decide
  have hdescent : baseEnd_5243713 < baseStart_5243713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243726 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2]
def baseStart_5243726 : Nat := 118140960795 + 5243726 * 2 ^ 59
def prefixEnd_5243726 : Nat := 4983230072969 + 3 ^ 40 * 5243726 * 2
def baseEnd_5243726 : Nat := 2692551858478256131609549

theorem tailTrace_5243726 : CollatzResearch.WordTrace tailWord_5243726 prefixEnd_5243726 2692551858478256131609549 := by
  unfold tailWord_5243726
  simp only [CollatzResearch.WordTrace]
  refine ⟨23906799925110466743370879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127502932933922489297978021 23906799925110466743370879)
  ·
    refine ⟨35860199887665700115056319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23906799925110466743370879 35860199887665700115056319)
    ·
      refine ⟨53790299831498550172584479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35860199887665700115056319 53790299831498550172584479)
      ·
        refine ⟨80685449747247825258876719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53790299831498550172584479 80685449747247825258876719)
        ·
          refine ⟨121028174620871737888315079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80685449747247825258876719 121028174620871737888315079)
          ·
            refine ⟨181542261931307606832472619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121028174620871737888315079 181542261931307606832472619)
            ·
              refine ⟨272313392896961410248708929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181542261931307606832472619 272313392896961410248708929)
              ·
                refine ⟨204235044672721057686531697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272313392896961410248708929 204235044672721057686531697)
                ·
                  refine ⟨153176283504540793264898773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204235044672721057686531697 153176283504540793264898773)
                  ·
                    refine ⟨3590069144637674842146065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 153176283504540793264898773 3590069144637674842146065)
                    ·
                      refine ⟨2692551858478256131609549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3590069144637674842146065 2692551858478256131609549)
                      ·
                        rfl

theorem cell23_5243726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_5243726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243726 prefixEnd_5243726 := by exact prefixLift 5243726
  have htrace : WordTrace (prefixWord ++ tailWord_5243726) baseStart_5243726 baseEnd_5243726 := by
    simpa [prefixWord, tailWord_5243726, baseEnd_5243726] using wordTrace_append hprefix tailTrace_5243726
  have hstable : (prefixWord ++ tailWord_5243726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243726).length < 2 ^ (prefixWord ++ tailWord_5243726).sum := by decide
  have hdescent : baseEnd_5243726 < baseStart_5243726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243743 : List Nat := [1, 1, 2, 3, 1, 3, 1, 5, 1, 3, 2]
def baseStart_5243743 : Nat := 118140960795 + 5243743 * 2 ^ 59
def prefixEnd_5243743 : Nat := 4983230072969 + 3 ^ 40 * 5243743 * 2
def baseEnd_5243743 : Nat := 2692560587649382565096971

theorem tailTrace_5243743 : CollatzResearch.WordTrace tailWord_5243743 prefixEnd_5243743 2692560587649382565096971 := by
  unfold tailWord_5243743
  simp only [CollatzResearch.WordTrace]
  refine ⟨191255019441822145850335883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127503346294548097233557255 191255019441822145850335883)
  ·
    refine ⟨286882529162733218775503825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191255019441822145850335883 286882529162733218775503825)
    ·
      refine ⟨215161896872049914081627869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286882529162733218775503825 215161896872049914081627869)
      ·
        refine ⟨80685711327018717780610451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215161896872049914081627869 80685711327018717780610451)
        ·
          refine ⟨121028566990528076670915677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80685711327018717780610451 121028566990528076670915677)
          ·
            refine ⟨45385712621448028751593379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121028566990528076670915677 45385712621448028751593379)
            ·
              refine ⟨68078568932172043127390069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45385712621448028751593379 68078568932172043127390069)
              ·
                refine ⟨6382365837391129043192819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68078568932172043127390069 6382365837391129043192819)
                ·
                  refine ⟨9573548756086693564789229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6382365837391129043192819 9573548756086693564789229)
                  ·
                    refine ⟨3590080783532510086795961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9573548756086693564789229 3590080783532510086795961)
                    ·
                      refine ⟨2692560587649382565096971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3590080783532510086795961 2692560587649382565096971)
                      ·
                        rfl

theorem cell23_5243743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_5243743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243743 prefixEnd_5243743 := by exact prefixLift 5243743
  have htrace : WordTrace (prefixWord ++ tailWord_5243743) baseStart_5243743 baseEnd_5243743 := by
    simpa [prefixWord, tailWord_5243743, baseEnd_5243743] using wordTrace_append hprefix tailTrace_5243743
  have hstable : (prefixWord ++ tailWord_5243743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243743).length < 2 ^ (prefixWord ++ tailWord_5243743).sum := by decide
  have hdescent : baseEnd_5243743 < baseStart_5243743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243749 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 4, 6]
def baseStart_5243749 : Nat := 118140960795 + 5243749 * 2 ^ 59
def prefixEnd_5243749 : Nat := 4983230072969 + 3 ^ 40 * 5243749 * 2
def baseEnd_5243749 : Nat := 897521222844436513873981

theorem tailTrace_5243749 : CollatzResearch.WordTrace tailWord_5243749 prefixEnd_5243749 897521222844436513873981 := by
  unfold tailWord_5243749
  simp only [CollatzResearch.WordTrace]
  refine ⟨191255238279800408875054301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127503492186533605916702867 191255238279800408875054301)
  ·
    refine ⟨71720714354925153328145363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191255238279800408875054301 71720714354925153328145363)
    ·
      refine ⟨107581071532387729992218045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71720714354925153328145363 107581071532387729992218045)
      ·
        refine ⟨40342901824645398747081767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107581071532387729992218045 40342901824645398747081767)
        ·
          refine ⟨60514352736968098120622651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40342901824645398747081767 60514352736968098120622651)
          ·
            refine ⟨90771529105452147180933977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60514352736968098120622651 90771529105452147180933977)
            ·
              refine ⟨68078646829089110385700483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90771529105452147180933977 68078646829089110385700483)
              ·
                refine ⟨102117970243633665578550725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68078646829089110385700483 102117970243633665578550725)
                ·
                  refine ⟨19147119420681312295978261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102117970243633665578550725 19147119420681312295978261)
                  ·
                    refine ⟨897521222844436513873981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19147119420681312295978261 897521222844436513873981)
                    ·
                      rfl

theorem cell23_5243749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_5243749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243749 prefixEnd_5243749 := by exact prefixLift 5243749
  have htrace : WordTrace (prefixWord ++ tailWord_5243749) baseStart_5243749 baseEnd_5243749 := by
    simpa [prefixWord, tailWord_5243749, baseEnd_5243749] using wordTrace_append hprefix tailTrace_5243749
  have hstable : (prefixWord ++ tailWord_5243749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243749).length < 2 ^ (prefixWord ++ tailWord_5243749).sum := by decide
  have hdescent : baseEnd_5243749 < baseStart_5243749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243779 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 9]
def baseStart_5243779 : Nat := 118140960795 + 5243779 * 2 ^ 59
def prefixEnd_5243779 : Nat := 4983230072969 + 3 ^ 40 * 5243779 * 2
def baseEnd_5243779 : Nat := 299175452550327158249645

theorem tailTrace_5243779 : CollatzResearch.WordTrace tailWord_5243779 prefixEnd_5243779 299175452550327158249645 := by
  unfold tailWord_5243779
  simp only [CollatzResearch.WordTrace]
  refine ⟨191256332469691723998646391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127504221646461149332430927 191256332469691723998646391)
  ·
    refine ⟨286884498704537585997969587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191256332469691723998646391 286884498704537585997969587)
    ·
      refine ⟨430326748056806378996954381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286884498704537585997969587 430326748056806378996954381)
      ·
        refine ⟨161372530521302392123857893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430326748056806378996954381 161372530521302392123857893)
        ·
          refine ⟨30257349472744198523223355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161372530521302392123857893 30257349472744198523223355)
          ·
            refine ⟨45386024209116297784835033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30257349472744198523223355 45386024209116297784835033)
            ·
              refine ⟨34039518156837223338626275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45386024209116297784835033 34039518156837223338626275)
              ·
                refine ⟨51059277235255835007939413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34039518156837223338626275 51059277235255835007939413)
                ·
                  refine ⟨299175452550327158249645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51059277235255835007939413 299175452550327158249645)
                  ·
                    rfl

theorem cell23_5243779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 9].length) (baseStart_5243779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243779 prefixEnd_5243779 := by exact prefixLift 5243779
  have htrace : WordTrace (prefixWord ++ tailWord_5243779) baseStart_5243779 baseEnd_5243779 := by
    simpa [prefixWord, tailWord_5243779, baseEnd_5243779] using wordTrace_append hprefix tailTrace_5243779
  have hstable : (prefixWord ++ tailWord_5243779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243779).length < 2 ^ (prefixWord ++ tailWord_5243779).sum := by decide
  have hdescent : baseEnd_5243779 < baseStart_5243779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243794 : List Nat := [3, 2, 3, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_5243794 : Nat := 118140960795 + 5243794 * 2 ^ 59
def prefixEnd_5243794 : Nat := 4983230072969 + 3 ^ 40 * 5243794 * 2
def baseEnd_5243794 : Nat := 2692586775162761865559237

theorem tailTrace_5243794 : CollatzResearch.WordTrace tailWord_5243794 prefixEnd_5243794 2692586775162761865559237 := by
  unfold tailWord_5243794
  simp only [CollatzResearch.WordTrace]
  refine ⟨47814219891159345390110609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127504586376424921040294957 47814219891159345390110609)
  ·
    refine ⟨35860664918369509042582957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47814219891159345390110609 35860664918369509042582957)
    ·
      refine ⟨13447749344388565890968609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35860664918369509042582957 13447749344388565890968609)
      ·
        refine ⟨10085812008291424418226457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13447749344388565890968609 10085812008291424418226457)
        ·
          refine ⟨7564359006218568313669843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10085812008291424418226457 7564359006218568313669843)
          ·
            refine ⟨11346538509327852470504765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7564359006218568313669843 11346538509327852470504765)
            ·
              refine ⟨4254951940997944676439287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11346538509327852470504765 4254951940997944676439287)
              ·
                refine ⟨6382427911496917014658931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4254951940997944676439287 6382427911496917014658931)
                ·
                  refine ⟨9573641867245375521988397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6382427911496917014658931 9573641867245375521988397)
                  ·
                    refine ⟨3590115700217015820745649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9573641867245375521988397 3590115700217015820745649)
                    ·
                      refine ⟨2692586775162761865559237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3590115700217015820745649 2692586775162761865559237)
                      ·
                        rfl

theorem cell23_5243794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_5243794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243794 prefixEnd_5243794 := by exact prefixLift 5243794
  have htrace : WordTrace (prefixWord ++ tailWord_5243794) baseStart_5243794 baseEnd_5243794 := by
    simpa [prefixWord, tailWord_5243794, baseEnd_5243794] using wordTrace_append hprefix tailTrace_5243794
  have hstable : (prefixWord ++ tailWord_5243794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243794).length < 2 ^ (prefixWord ++ tailWord_5243794).sum := by decide
  have hdescent : baseEnd_5243794 < baseStart_5243794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243807 : List Nat := [1, 1, 2, 5, 2, 2, 2, 2, 2, 2, 2]
def baseStart_5243807 : Nat := 118140960795 + 5243807 * 2 ^ 59
def prefixEnd_5243807 : Nat := 4983230072969 + 3 ^ 40 * 5243807 * 2
def baseEnd_5243807 : Nat := 2692593450411270314696677

theorem tailTrace_5243807 : CollatzResearch.WordTrace tailWord_5243807 prefixEnd_5243807 2692593450411270314696677 := by
  unfold tailWord_5243807
  simp only [CollatzResearch.WordTrace]
  refine ⟨191257353713590284780665675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127504902475726856520443783 191257353713590284780665675)
  ·
    refine ⟨286886030570385427170998513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191257353713590284780665675 286886030570385427170998513)
    ·
      refine ⟨215164522927789070378248885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286886030570385427170998513 215164522927789070378248885)
      ·
        refine ⟨20171674024480225347960833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215164522927789070378248885 20171674024480225347960833)
        ·
          refine ⟨15128755518360169010970625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20171674024480225347960833 15128755518360169010970625)
          ·
            refine ⟨11346566638770126758227969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15128755518360169010970625 11346566638770126758227969)
            ·
              refine ⟨8509924979077595068670977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11346566638770126758227969 8509924979077595068670977)
              ·
                refine ⟨6382443734308196301503233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8509924979077595068670977 6382443734308196301503233)
                ·
                  refine ⟨4786832800731147226127425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6382443734308196301503233 4786832800731147226127425)
                  ·
                    refine ⟨3590124600548360419595569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4786832800731147226127425 3590124600548360419595569)
                    ·
                      refine ⟨2692593450411270314696677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3590124600548360419595569 2692593450411270314696677)
                      ·
                        rfl

theorem cell23_5243807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_5243807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243807 prefixEnd_5243807 := by exact prefixLift 5243807
  have htrace : WordTrace (prefixWord ++ tailWord_5243807) baseStart_5243807 baseEnd_5243807 := by
    simpa [prefixWord, tailWord_5243807, baseEnd_5243807] using wordTrace_append hprefix tailTrace_5243807
  have hstable : (prefixWord ++ tailWord_5243807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243807).length < 2 ^ (prefixWord ++ tailWord_5243807).sum := by decide
  have hdescent : baseEnd_5243807 < baseStart_5243807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5243839 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 1, 10]
def baseStart_5243839 : Nat := 118140960795 + 5243839 * 2 ^ 59
def prefixEnd_5243839 : Nat := 4983230072969 + 3 ^ 40 * 5243839 * 2
def baseEnd_5243839 : Nat := 897536627264071396498843

theorem tailTrace_5243839 : CollatzResearch.WordTrace tailWord_5243839 prefixEnd_5243839 897536627264071396498843 := by
  unfold tailWord_5243839
  simp only [CollatzResearch.WordTrace]
  refine ⟨191258520849474354245830571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127505680566316236163887047 191258520849474354245830571)
  ·
    refine ⟨286887781274211531368745857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191258520849474354245830571 286887781274211531368745857)
    ·
      refine ⟨215165835955658648526559393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286887781274211531368745857 215165835955658648526559393)
      ·
        refine ⟨161374376966743986394919545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215165835955658648526559393 161374376966743986394919545)
        ·
          refine ⟨121030782725057989796189659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161374376966743986394919545 121030782725057989796189659)
          ·
            refine ⟨181546174087586984694284489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121030782725057989796189659 181546174087586984694284489)
            ·
              refine ⟨136159630565690238520713367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181546174087586984694284489 136159630565690238520713367)
              ·
                refine ⟨204239445848535357781070051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136159630565690238520713367 204239445848535357781070051)
                ·
                  refine ⟨306359168772803036671605077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204239445848535357781070051 306359168772803036671605077)
                  ·
                    refine ⟨897536627264071396498843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 306359168772803036671605077 897536627264071396498843)
                    ·
                      rfl

theorem cell23_5243839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_5243839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5243839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5243839 prefixEnd_5243839 := by exact prefixLift 5243839
  have htrace : WordTrace (prefixWord ++ tailWord_5243839) baseStart_5243839 baseEnd_5243839 := by
    simpa [prefixWord, tailWord_5243839, baseEnd_5243839] using wordTrace_append hprefix tailTrace_5243839
  have hstable : (prefixWord ++ tailWord_5243839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5243839).length < 2 ^ (prefixWord ++ tailWord_5243839).sum := by decide
  have hdescent : baseEnd_5243839 < baseStart_5243839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5243839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
