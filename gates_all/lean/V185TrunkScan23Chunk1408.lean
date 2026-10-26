import V185TrunkScan23Chunk1407

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8340256 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 4, 2, 2]
def baseStart_8340256 : Nat := 118140960795 + 8340256 * 2 ^ 59
def prefixEnd_8340256 : Nat := 4983230072969 + 3 ^ 40 * 8340256 * 2
def baseEnd_8340256 : Nat := 4282560109545025943743867

theorem tailTrace_8340256 : CollatzResearch.WordTrace tailWord_8340256 prefixEnd_8340256 4282560109545025943743867 := by
  unfold tailWord_8340256
  simp only [CollatzResearch.WordTrace]
  refine ⟨152097063436342194583724311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202796084581789592778299081 152097063436342194583724311)
  ·
    refine ⟨228145595154513291875586467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152097063436342194583724311 228145595154513291875586467)
    ·
      refine ⟨342218392731769937813379701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228145595154513291875586467 342218392731769937813379701)
      ·
        refine ⟨32082974318603431670004347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 342218392731769937813379701 32082974318603431670004347)
        ·
          refine ⟨48124461477905147505006521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32082974318603431670004347 48124461477905147505006521)
          ·
            refine ⟨36093346108428860628754891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48124461477905147505006521 36093346108428860628754891)
            ·
              refine ⟨54140019162643290943132337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36093346108428860628754891 54140019162643290943132337)
              ·
                refine ⟨40605014371982468207349253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54140019162643290943132337 40605014371982468207349253)
                ·
                  refine ⟨7613440194746712788877985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40605014371982468207349253 7613440194746712788877985)
                  ·
                    refine ⟨5710080146060034591658489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7613440194746712788877985 5710080146060034591658489)
                    ·
                      refine ⟨4282560109545025943743867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5710080146060034591658489 4282560109545025943743867)
                      ·
                        rfl

theorem cell23_8340256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_8340256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340256 prefixEnd_8340256 := by exact prefixLift 8340256
  have htrace : WordTrace (prefixWord ++ tailWord_8340256) baseStart_8340256 baseEnd_8340256 := by
    simpa [prefixWord, tailWord_8340256, baseEnd_8340256] using wordTrace_append hprefix tailTrace_8340256
  have hstable : (prefixWord ++ tailWord_8340256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340256).length < 2 ^ (prefixWord ++ tailWord_8340256).sum := by decide
  have hdescent : baseEnd_8340256 < baseStart_8340256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340272 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 3]
def baseStart_8340272 : Nat := 118140960795 + 8340272 * 2 ^ 59
def prefixEnd_8340272 : Nat := 4983230072969 + 3 ^ 40 * 8340272 * 2
def baseEnd_8340272 : Nat := 4282568325235497881143793

theorem tailTrace_8340272 : CollatzResearch.WordTrace tailWord_8340272 prefixEnd_8340272 4282568325235497881143793 := by
  unfold tailWord_8340272
  simp only [CollatzResearch.WordTrace]
  refine ⟨152097355220313211950015535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202796473627084282600020713 152097355220313211950015535)
  ·
    refine ⟨228146032830469817925023303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152097355220313211950015535 228146032830469817925023303)
    ·
      refine ⟨342219049245704726887534955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228146032830469817925023303 342219049245704726887534955)
      ·
        refine ⟨513328573868557090331302433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342219049245704726887534955 513328573868557090331302433)
        ·
          refine ⟨384996430401417817748476825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513328573868557090331302433 384996430401417817748476825)
          ·
            refine ⟨288747322801063363311357619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384996430401417817748476825 288747322801063363311357619)
            ·
              refine ⟨433120984201595044967036429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288747322801063363311357619 433120984201595044967036429)
              ·
                refine ⟨162420369075598141862638661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433120984201595044967036429 162420369075598141862638661)
                ·
                  refine ⟨30453819201674651599244749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162420369075598141862638661 30453819201674651599244749)
                  ·
                    refine ⟨11420182200627994349716781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30453819201674651599244749 11420182200627994349716781)
                    ·
                      refine ⟨4282568325235497881143793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11420182200627994349716781 4282568325235497881143793)
                      ·
                        rfl

theorem cell23_8340272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 3].length) (baseStart_8340272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340272 prefixEnd_8340272 := by exact prefixLift 8340272
  have htrace : WordTrace (prefixWord ++ tailWord_8340272) baseStart_8340272 baseEnd_8340272 := by
    simpa [prefixWord, tailWord_8340272, baseEnd_8340272] using wordTrace_append hprefix tailTrace_8340272
  have hstable : (prefixWord ++ tailWord_8340272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340272).length < 2 ^ (prefixWord ++ tailWord_8340272).sum := by decide
  have hdescent : baseEnd_8340272 < baseStart_8340272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340294 : List Nat := [6, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_8340294 : Nat := 118140960795 + 8340294 * 2 ^ 59
def prefixEnd_8340294 : Nat := 4983230072969 + 3 ^ 40 * 8340294 * 2
def baseEnd_8340294 : Nat := 4282579621809896795068693

theorem tailTrace_8340294 : CollatzResearch.WordTrace tailWord_8340294 prefixEnd_8340294 4282579621809896795068693 := by
  unfold tailWord_8340294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9506109776454585051791623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202797008564364481104887957 9506109776454585051791623)
  ·
    refine ⟨14259164664681877577687435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9506109776454585051791623 14259164664681877577687435)
    ·
      refine ⟨21388746997022816366531153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14259164664681877577687435 21388746997022816366531153)
      ·
        refine ⟨16041560247767112274898365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21388746997022816366531153 16041560247767112274898365)
        ·
          refine ⟨6015585092912667103086887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16041560247767112274898365 6015585092912667103086887)
          ·
            refine ⟨9023377639369000654630331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6015585092912667103086887 9023377639369000654630331)
            ·
              refine ⟨13535066459053500981945497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9023377639369000654630331 13535066459053500981945497)
              ·
                refine ⟨10151299844290125736459123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13535066459053500981945497 10151299844290125736459123)
                ·
                  refine ⟨15226949766435188604688685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10151299844290125736459123 15226949766435188604688685)
                  ·
                    refine ⟨5710106162413195726758257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15226949766435188604688685 5710106162413195726758257)
                    ·
                      refine ⟨4282579621809896795068693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5710106162413195726758257 4282579621809896795068693)
                      ·
                        rfl

theorem cell23_8340294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_8340294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340294 prefixEnd_8340294 := by exact prefixLift 8340294
  have htrace : WordTrace (prefixWord ++ tailWord_8340294) baseStart_8340294 baseEnd_8340294 := by
    simpa [prefixWord, tailWord_8340294, baseEnd_8340294] using wordTrace_append hprefix tailTrace_8340294
  have hstable : (prefixWord ++ tailWord_8340294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340294).length < 2 ^ (prefixWord ++ tailWord_8340294).sum := by decide
  have hdescent : baseEnd_8340294 < baseStart_8340294 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340309 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 2, 5]
def baseStart_8340309 : Nat := 118140960795 + 8340309 * 2 ^ 59
def prefixEnd_8340309 : Nat := 4983230072969 + 3 ^ 40 * 8340309 * 2
def baseEnd_8340309 : Nat := 1427529108006571412127041

theorem tailTrace_8340309 : CollatzResearch.WordTrace tailWord_8340309 prefixEnd_8340309 1427529108006571412127041 := by
  unfold tailWord_8340309
  simp only [CollatzResearch.WordTrace]
  refine ⟨304196059941492379219127981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202797373294328252812751987 304196059941492379219127981)
  ·
    refine ⟨114073522478059642207172993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304196059941492379219127981 114073522478059642207172993)
    ·
      refine ⟨85555141858544731655379745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114073522478059642207172993 85555141858544731655379745)
      ·
        refine ⟨64166356393908548741534809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85555141858544731655379745 64166356393908548741534809)
        ·
          refine ⟨48124767295431411556151107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64166356393908548741534809 48124767295431411556151107)
          ·
            refine ⟨72187150943147117334226661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48124767295431411556151107 72187150943147117334226661)
            ·
              refine ⟨13535090801840084500167499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72187150943147117334226661 13535090801840084500167499)
              ·
                refine ⟨20302636202760126750251249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13535090801840084500167499 20302636202760126750251249)
                ·
                  refine ⟨15226977152070095062688437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20302636202760126750251249 15226977152070095062688437)
                  ·
                    refine ⟨1427529108006571412127041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15226977152070095062688437 1427529108006571412127041)
                    ·
                      rfl

theorem cell23_8340309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_8340309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340309 prefixEnd_8340309 := by exact prefixLift 8340309
  have htrace : WordTrace (prefixWord ++ tailWord_8340309) baseStart_8340309 baseEnd_8340309 := by
    simpa [prefixWord, tailWord_8340309, baseEnd_8340309] using wordTrace_append hprefix tailTrace_8340309
  have hstable : (prefixWord ++ tailWord_8340309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340309).length < 2 ^ (prefixWord ++ tailWord_8340309).sum := by decide
  have hdescent : baseEnd_8340309 < baseStart_8340309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340312 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_8340312 : Nat := 118140960795 + 8340312 * 2 ^ 59
def prefixEnd_8340312 : Nat := 4983230072969 + 3 ^ 40 * 8340312 * 2
def baseEnd_8340312 : Nat := 4282588864461677724643609

theorem tailTrace_8340312 : CollatzResearch.WordTrace tailWord_8340312 prefixEnd_8340312 4282588864461677724643609 := by
  unfold tailWord_8340312
  simp only [CollatzResearch.WordTrace]
  refine ⟨152098084680240755365743595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202797446240321007154324793 152098084680240755365743595)
  ·
    refine ⟨228147127020361133048615393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152098084680240755365743595 228147127020361133048615393)
    ·
      refine ⟨171110345265270849786461545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228147127020361133048615393 171110345265270849786461545)
      ·
        refine ⟨128332758948953137339846159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171110345265270849786461545 128332758948953137339846159)
        ·
          refine ⟨192499138423429706009769239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128332758948953137339846159 192499138423429706009769239)
          ·
            refine ⟨288748707635144559014653859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192499138423429706009769239 288748707635144559014653859)
            ·
              refine ⟨433123061452716838521980789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288748707635144559014653859 433123061452716838521980789)
              ·
                refine ⟨40605287011192203611435699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 433123061452716838521980789 40605287011192203611435699)
                ·
                  refine ⟨60907930516788305417153549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40605287011192203611435699 60907930516788305417153549)
                  ·
                    refine ⟨22840473943795614531432581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60907930516788305417153549 22840473943795614531432581)
                    ·
                      refine ⟨4282588864461677724643609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22840473943795614531432581 4282588864461677724643609)
                      ·
                        rfl

theorem cell23_8340312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_8340312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340312 prefixEnd_8340312 := by exact prefixLift 8340312
  have htrace : WordTrace (prefixWord ++ tailWord_8340312) baseStart_8340312 baseEnd_8340312 := by
    simpa [prefixWord, tailWord_8340312, baseEnd_8340312] using wordTrace_append hprefix tailTrace_8340312
  have hstable : (prefixWord ++ tailWord_8340312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340312).length < 2 ^ (prefixWord ++ tailWord_8340312).sum := by decide
  have hdescent : baseEnd_8340312 < baseStart_8340312 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340332 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_8340332 : Nat := 118140960795 + 8340332 * 2 ^ 59
def prefixEnd_8340332 : Nat := 4983230072969 + 3 ^ 40 * 8340332 * 2
def baseEnd_8340332 : Nat := 4282599134074767646393517

theorem tailTrace_8340332 : CollatzResearch.WordTrace tailWord_8340332 prefixEnd_8340332 4282599134074767646393517 := by
  unfold tailWord_8340332
  simp only [CollatzResearch.WordTrace]
  refine ⟨152098449410204527073607625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202797932546939369431476833 152098449410204527073607625)
  ·
    refine ⟨114073837057653395305205719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152098449410204527073607625 114073837057653395305205719)
    ·
      refine ⟨171110755586480092957808579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114073837057653395305205719 171110755586480092957808579)
      ·
        refine ⟨256666133379720139436712869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171110755586480092957808579 256666133379720139436712869)
        ·
          refine ⟨48124900008697526144383663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256666133379720139436712869 48124900008697526144383663)
          ·
            refine ⟨72187350013046289216575495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48124900008697526144383663 72187350013046289216575495)
            ·
              refine ⟨108281025019569433824863243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72187350013046289216575495 108281025019569433824863243)
              ·
                refine ⟨162421537529354150737294865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108281025019569433824863243 162421537529354150737294865)
                ·
                  refine ⟨121816153147015613052971149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162421537529354150737294865 121816153147015613052971149)
                  ·
                    refine ⟨45681057430130854894864181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121816153147015613052971149 45681057430130854894864181)
                    ·
                      refine ⟨4282599134074767646393517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45681057430130854894864181 4282599134074767646393517)
                      ·
                        rfl

theorem cell23_8340332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_8340332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340332 prefixEnd_8340332 := by exact prefixLift 8340332
  have htrace : WordTrace (prefixWord ++ tailWord_8340332) baseStart_8340332 baseEnd_8340332 := by
    simpa [prefixWord, tailWord_8340332, baseEnd_8340332] using wordTrace_append hprefix tailTrace_8340332
  have hstable : (prefixWord ++ tailWord_8340332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340332).length < 2 ^ (prefixWord ++ tailWord_8340332).sum := by decide
  have hdescent : baseEnd_8340332 < baseStart_8340332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340349 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_8340349 : Nat := 118140960795 + 8340349 * 2 ^ 59
def prefixEnd_8340349 : Nat := 4983230072969 + 3 ^ 40 * 8340349 * 2
def baseEnd_8340349 : Nat := 4282607863245894079880939

theorem tailTrace_8340349 : CollatzResearch.WordTrace tailWord_8340349 prefixEnd_8340349 4282607863245894079880939 := by
  unfold tailWord_8340349
  simp only [CollatzResearch.WordTrace]
  refine ⟨304197518861347466050584101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202798345907564977367056067 304197518861347466050584101)
  ·
    refine ⟨57037034786502649884484519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304197518861347466050584101 57037034786502649884484519)
    ·
      refine ⟨85555552179753974826726779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57037034786502649884484519 85555552179753974826726779)
      ·
        refine ⟨128333328269630962240090169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85555552179753974826726779 128333328269630962240090169)
        ·
          refine ⟨96249996202223221680067627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128333328269630962240090169 96249996202223221680067627)
          ·
            refine ⟨144374994303334832520101441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96249996202223221680067627 144374994303334832520101441)
            ·
              refine ⟨108281245727501124390076081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144374994303334832520101441 108281245727501124390076081)
              ·
                refine ⟨81210934295625843292557061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108281245727501124390076081 81210934295625843292557061)
                ·
                  refine ⟨15227050180429845617354449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81210934295625843292557061 15227050180429845617354449)
                  ·
                    refine ⟨11420287635322384213015837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15227050180429845617354449 11420287635322384213015837)
                    ·
                      refine ⟨4282607863245894079880939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11420287635322384213015837 4282607863245894079880939)
                      ·
                        rfl

theorem cell23_8340349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_8340349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340349 prefixEnd_8340349 := by exact prefixLift 8340349
  have htrace : WordTrace (prefixWord ++ tailWord_8340349) baseStart_8340349 baseEnd_8340349 := by
    simpa [prefixWord, tailWord_8340349, baseEnd_8340349] using wordTrace_append hprefix tailTrace_8340349
  have hstable : (prefixWord ++ tailWord_8340349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340349).length < 2 ^ (prefixWord ++ tailWord_8340349).sum := by decide
  have hdescent : baseEnd_8340349 < baseStart_8340349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340373 : List Nat := [1, 3, 2, 1, 1, 5, 2, 3, 1, 4]
def baseStart_8340373 : Nat := 118140960795 + 8340373 * 2 ^ 59
def prefixEnd_8340373 : Nat := 4983230072969 + 3 ^ 40 * 8340373 * 2
def baseEnd_8340373 : Nat := 1427540062260533995326943

theorem tailTrace_8340373 : CollatzResearch.WordTrace tailWord_8340373 prefixEnd_8340373 1427540062260533995326943 := by
  unfold tailWord_8340373
  simp only [CollatzResearch.WordTrace]
  refine ⟨304198394213260518149457773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202798929475507012099638515 304198394213260518149457773)
  ·
    refine ⟨114074397829972694306046665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304198394213260518149457773 114074397829972694306046665)
    ·
      refine ⟨85555798372479520729534999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114074397829972694306046665 85555798372479520729534999)
      ·
        refine ⟨128333697558719281094302499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85555798372479520729534999 128333697558719281094302499)
        ·
          refine ⟨192500546338078921641453749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128333697558719281094302499 192500546338078921641453749)
          ·
            refine ⟨18046926219194898903886289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192500546338078921641453749 18046926219194898903886289)
            ·
              refine ⟨13535194664396174177914717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18046926219194898903886289 13535194664396174177914717)
              ·
                refine ⟨5075697999148565316718019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13535194664396174177914717 5075697999148565316718019)
                ·
                  refine ⟨7613546998722847975077029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075697999148565316718019 7613546998722847975077029)
                  ·
                    refine ⟨1427540062260533995326943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7613546998722847975077029 1427540062260533995326943)
                    ·
                      rfl

theorem cell23_8340373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_8340373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340373 prefixEnd_8340373 := by exact prefixLift 8340373
  have htrace : WordTrace (prefixWord ++ tailWord_8340373) baseStart_8340373 baseEnd_8340373 := by
    simpa [prefixWord, tailWord_8340373, baseEnd_8340373] using wordTrace_append hprefix tailTrace_8340373
  have hstable : (prefixWord ++ tailWord_8340373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340373).length < 2 ^ (prefixWord ++ tailWord_8340373).sum := by decide
  have hdescent : baseEnd_8340373 < baseStart_8340373 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340386 : List Nat := [3, 3, 1, 2, 2, 1, 3, 2, 6]
def baseStart_8340386 : Nat := 118140960795 + 8340386 * 2 ^ 59
def prefixEnd_8340386 : Nat := 4983230072969 + 3 ^ 40 * 8340386 * 2
def baseEnd_8340386 : Nat := 475847429114456715013141

theorem tailTrace_8340386 : CollatzResearch.WordTrace tailWord_8340386 prefixEnd_8340386 475847429114456715013141 := by
  unfold tailWord_8340386
  simp only [CollatzResearch.WordTrace]
  refine ⟨76049717090553355342420253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202799245574808947579787341 76049717090553355342420253)
  ·
    refine ⟨28518643908957508253407595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76049717090553355342420253 28518643908957508253407595)
    ·
      refine ⟨42777965863436262380111393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28518643908957508253407595 42777965863436262380111393)
      ·
        refine ⟨32083474397577196785083545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42777965863436262380111393 32083474397577196785083545)
        ·
          refine ⟨24062605798182897588812659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32083474397577196785083545 24062605798182897588812659)
          ·
            refine ⟨36093908697274346383218989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24062605798182897588812659 36093908697274346383218989)
            ·
              refine ⟨13535215761477879893707121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36093908697274346383218989 13535215761477879893707121)
              ·
                refine ⟨10151411821108409920280341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13535215761477879893707121 10151411821108409920280341)
                ·
                  refine ⟨475847429114456715013141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10151411821108409920280341 475847429114456715013141)
                  ·
                    rfl

theorem cell23_8340386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_8340386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340386 prefixEnd_8340386 := by exact prefixLift 8340386
  have htrace : WordTrace (prefixWord ++ tailWord_8340386) baseStart_8340386 baseEnd_8340386 := by
    simpa [prefixWord, tailWord_8340386, baseEnd_8340386] using wordTrace_append hprefix tailTrace_8340386
  have hstable : (prefixWord ++ tailWord_8340386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340386).length < 2 ^ (prefixWord ++ tailWord_8340386).sum := by decide
  have hdescent : baseEnd_8340386 < baseStart_8340386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340416 : List Nat := [2, 1, 1, 2, 3, 4, 2, 2, 1, 5]
def baseStart_8340416 : Nat := 118140960795 + 8340416 * 2 ^ 59
def prefixEnd_8340416 : Nat := 4983230072969 + 3 ^ 40 * 8340416 * 2
def baseEnd_8340416 : Nat := 1427547422149915105914377

theorem tailTrace_8340416 : CollatzResearch.WordTrace tailWord_8340416 prefixEnd_8340416 1427547422149915105914377 := by
  unfold tailWord_8340416
  simp only [CollatzResearch.WordTrace]
  refine ⟨152099981276052368246636551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202799975034736490995515401 152099981276052368246636551)
  ·
    refine ⟨228149971914078552369954827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152099981276052368246636551 228149971914078552369954827)
    ·
      refine ⟨342224957871117828554932241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228149971914078552369954827 342224957871117828554932241)
      ·
        refine ⟨256668718403338371416199181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342224957871117828554932241 256668718403338371416199181)
        ·
          refine ⟨96250769401251889281074693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256668718403338371416199181 96250769401251889281074693)
          ·
            refine ⟨18047019262734729240201505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96250769401251889281074693 18047019262734729240201505)
            ·
              refine ⟨13535264447051046930151129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18047019262734729240201505 13535264447051046930151129)
              ·
                refine ⟨10151448335288285197613347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13535264447051046930151129 10151448335288285197613347)
                ·
                  refine ⟨15227172502932427796420021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10151448335288285197613347 15227172502932427796420021)
                  ·
                    refine ⟨1427547422149915105914377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15227172502932427796420021 1427547422149915105914377)
                    ·
                      rfl

theorem cell23_8340416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 1, 5].length) (baseStart_8340416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340416 prefixEnd_8340416 := by exact prefixLift 8340416
  have htrace : WordTrace (prefixWord ++ tailWord_8340416) baseStart_8340416 baseEnd_8340416 := by
    simpa [prefixWord, tailWord_8340416, baseEnd_8340416] using wordTrace_append hprefix tailTrace_8340416
  have hstable : (prefixWord ++ tailWord_8340416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340416).length < 2 ^ (prefixWord ++ tailWord_8340416).sum := by decide
  have hdescent : baseEnd_8340416 < baseStart_8340416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340430 : List Nat := [4, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3]
def baseStart_8340430 : Nat := 118140960795 + 8340430 * 2 ^ 59
def prefixEnd_8340430 : Nat := 4983230072969 + 3 ^ 40 * 8340430 * 2
def baseEnd_8340430 : Nat := 4282649455178908262968067

theorem tailTrace_8340430 : CollatzResearch.WordTrace tailWord_8340430 prefixEnd_8340430 4282649455178908262968067 := by
  unfold tailWord_8340430
  simp only [CollatzResearch.WordTrace]
  refine ⟨38025059146756752110535343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202800315449369344589521829 38025059146756752110535343)
  ·
    refine ⟨57037588720135128165803015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38025059146756752110535343 57037588720135128165803015)
    ·
      refine ⟨85556383080202692248704523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57037588720135128165803015 85556383080202692248704523)
      ·
        refine ⟨128334574620304038373056785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85556383080202692248704523 128334574620304038373056785)
        ·
          refine ⟨96250930965228028779792589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128334574620304038373056785 96250930965228028779792589)
          ·
            refine ⟨36094099111960510792422221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96250930965228028779792589 36094099111960510792422221)
            ·
              refine ⟨13535287166985191547158333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36094099111960510792422221 13535287166985191547158333)
              ·
                refine ⟨5075732687619446830184375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13535287166985191547158333 5075732687619446830184375)
                ·
                  refine ⟨7613599031429170245276563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075732687619446830184375 7613599031429170245276563)
                  ·
                    refine ⟨11420398547143755367914845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7613599031429170245276563 11420398547143755367914845)
                    ·
                      refine ⟨4282649455178908262968067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11420398547143755367914845 4282649455178908262968067)
                      ·
                        rfl

theorem cell23_8340430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_8340430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340430 prefixEnd_8340430 := by exact prefixLift 8340430
  have htrace : WordTrace (prefixWord ++ tailWord_8340430) baseStart_8340430 baseEnd_8340430 := by
    simpa [prefixWord, tailWord_8340430, baseEnd_8340430] using wordTrace_append hprefix tailTrace_8340430
  have hstable : (prefixWord ++ tailWord_8340430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340430).length < 2 ^ (prefixWord ++ tailWord_8340430).sum := by decide
  have hdescent : baseEnd_8340430 < baseStart_8340430 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340447 : List Nat := [1, 1, 2, 3, 5, 1, 3, 2, 1, 1, 3]
def baseStart_8340447 : Nat := 118140960795 + 8340447 * 2 ^ 59
def prefixEnd_8340447 : Nat := 4983230072969 + 3 ^ 40 * 8340447 * 2
def baseEnd_8340447 : Nat := 4282658184350034696455489

theorem tailTrace_8340447 : CollatzResearch.WordTrace tailWord_8340447 prefixEnd_8340447 4282658184350034696455489 := by
  unfold tailWord_8340447
  simp only [CollatzResearch.WordTrace]
  refine ⟨304201093214992428787651595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202800728809994952525101063 304201093214992428787651595)
  ·
    refine ⟨456301639822488643181477393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304201093214992428787651595 456301639822488643181477393)
    ·
      refine ⟨342226229866866482386108045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456301639822488643181477393 342226229866866482386108045)
      ·
        refine ⟨128334836200074930894790517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342226229866866482386108045 128334836200074930894790517)
        ·
          refine ⟨12031390893757024771386611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128334836200074930894790517 12031390893757024771386611)
          ·
            refine ⟨18047086340635537157079917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12031390893757024771386611 18047086340635537157079917)
            ·
              refine ⟨6767657377738326433904969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18047086340635537157079917 6767657377738326433904969)
              ·
                refine ⟨5075743033303744825428727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6767657377738326433904969 5075743033303744825428727)
                ·
                  refine ⟨7613614549955617238143091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075743033303744825428727 7613614549955617238143091)
                  ·
                    refine ⟨11420421824933425857214637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7613614549955617238143091 11420421824933425857214637)
                    ·
                      refine ⟨4282658184350034696455489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11420421824933425857214637 4282658184350034696455489)
                      ·
                        rfl

theorem cell23_8340447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_8340447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340447 prefixEnd_8340447 := by exact prefixLift 8340447
  have htrace : WordTrace (prefixWord ++ tailWord_8340447) baseStart_8340447 baseEnd_8340447 := by
    simpa [prefixWord, tailWord_8340447, baseEnd_8340447] using wordTrace_append hprefix tailTrace_8340447
  have hstable : (prefixWord ++ tailWord_8340447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340447).length < 2 ^ (prefixWord ++ tailWord_8340447).sum := by decide
  have hdescent : baseEnd_8340447 < baseStart_8340447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340463 : List Nat := [1, 1, 2, 1, 4, 3, 4, 1, 2, 4]
def baseStart_8340463 : Nat := 118140960795 + 8340463 * 2 ^ 59
def prefixEnd_8340463 : Nat := 4983230072969 + 3 ^ 40 * 8340463 * 2
def baseEnd_8340463 : Nat := 1427555466680168877951805

theorem tailTrace_8340463 : CollatzResearch.WordTrace tailWord_8340463 prefixEnd_8340463 1427555466680168877951805 := by
  unfold tailWord_8340463
  simp only [CollatzResearch.WordTrace]
  refine ⟨304201676782934463520234043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202801117855289642346822695 304201676782934463520234043)
  ·
    refine ⟨456302515174401695280351065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304201676782934463520234043 456302515174401695280351065)
    ·
      refine ⟨342226886380801271460263299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456302515174401695280351065 342226886380801271460263299)
      ·
        refine ⟨513340329571201907190394949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342226886380801271460263299 513340329571201907190394949)
        ·
          refine ⟨96251311794600357598199053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 513340329571201907190394949 96251311794600357598199053)
          ·
            refine ⟨36094241922975134099324645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96251311794600357598199053 36094241922975134099324645)
            ·
              refine ⟨6767670360557837643623371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36094241922975134099324645 6767670360557837643623371)
              ·
                refine ⟨10151505540836756465435057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6767670360557837643623371 10151505540836756465435057)
                ·
                  refine ⟨7613629155627567349076293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10151505540836756465435057 7613629155627567349076293)
                  ·
                    refine ⟨1427555466680168877951805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7613629155627567349076293 1427555466680168877951805)
                    ·
                      rfl

theorem cell23_8340463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 2, 4].length) (baseStart_8340463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340463 prefixEnd_8340463 := by exact prefixLift 8340463
  have htrace : WordTrace (prefixWord ++ tailWord_8340463) baseStart_8340463 baseEnd_8340463 := by
    simpa [prefixWord, tailWord_8340463, baseEnd_8340463] using wordTrace_append hprefix tailTrace_8340463
  have hstable : (prefixWord ++ tailWord_8340463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340463).length < 2 ^ (prefixWord ++ tailWord_8340463).sum := by decide
  have hdescent : baseEnd_8340463 < baseStart_8340463 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340470 : List Nat := [5, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_8340470 : Nat := 118140960795 + 8340470 * 2 ^ 59
def prefixEnd_8340470 : Nat := 4983230072969 + 3 ^ 40 * 8340470 * 2
def baseEnd_8340470 : Nat := 4282669994405088106467883

theorem tailTrace_8340470 : CollatzResearch.WordTrace tailWord_8340470 prefixEnd_8340470 4282669994405088106467883 := by
  unfold tailWord_8340470
  simp only [CollatzResearch.WordTrace]
  refine ⟨19012620755869318982233679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202801288062606069143825909 19012620755869318982233679)
  ·
    refine ⟨28518931133803978473350519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19012620755869318982233679 28518931133803978473350519)
    ·
      refine ⟨42778396700705967710025779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28518931133803978473350519 42778396700705967710025779)
      ·
        refine ⟨64167595051058951565038669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42778396700705967710025779 64167595051058951565038669)
        ·
          refine ⟨24062848144147106836889501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64167595051058951565038669 24062848144147106836889501)
          ·
            refine ⟨9023568054055165063833563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24062848144147106836889501 9023568054055165063833563)
            ·
              refine ⟨13535352081082747595750345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9023568054055165063833563 13535352081082747595750345)
              ·
                refine ⟨10151514060812060696812759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13535352081082747595750345 10151514060812060696812759)
                ·
                  refine ⟨15227271091218091045219139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10151514060812060696812759 15227271091218091045219139)
                  ·
                    refine ⟨22840906636827136567828709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15227271091218091045219139 22840906636827136567828709)
                    ·
                      refine ⟨4282669994405088106467883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22840906636827136567828709 4282669994405088106467883)
                      ·
                        rfl

theorem cell23_8340470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_8340470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340470 prefixEnd_8340470 := by exact prefixLift 8340470
  have htrace : WordTrace (prefixWord ++ tailWord_8340470) baseStart_8340470 baseEnd_8340470 := by
    simpa [prefixWord, tailWord_8340470, baseEnd_8340470] using wordTrace_append hprefix tailTrace_8340470
  have hstable : (prefixWord ++ tailWord_8340470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340470).length < 2 ^ (prefixWord ++ tailWord_8340470).sum := by decide
  have hdescent : baseEnd_8340470 < baseStart_8340470 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340490 : List Nat := [3, 1, 2, 2, 3, 2, 3, 1, 1, 2, 3]
def baseStart_8340490 : Nat := 118140960795 + 8340490 * 2 ^ 59
def prefixEnd_8340490 : Nat := 4983230072969 + 3 ^ 40 * 8340490 * 2
def baseEnd_8340490 : Nat := 4282680264018178028217791

theorem tailTrace_8340490 : CollatzResearch.WordTrace tailWord_8340490 prefixEnd_8340490 4282680264018178028217791 := by
  unfold tailWord_8340490
  simp only [CollatzResearch.WordTrace]
  refine ⟨76050665388459161782866731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202801774369224431420977949 76050665388459161782866731)
  ·
    refine ⟨114075998082688742674300097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76050665388459161782866731 114075998082688742674300097)
    ·
      refine ⟨85556998562016557005725073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114075998082688742674300097 85556998562016557005725073)
      ·
        refine ⟨64167748921512417754293805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85556998562016557005725073 64167748921512417754293805)
        ·
          refine ⟨24062905845567156657860177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64167748921512417754293805 24062905845567156657860177)
          ·
            refine ⟨18047179384175367493395133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24062905845567156657860177 18047179384175367493395133)
            ·
              refine ⟨6767692269065762810023175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18047179384175367493395133 6767692269065762810023175)
              ·
                refine ⟨10151538403598644215034763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6767692269065762810023175 10151538403598644215034763)
                ·
                  refine ⟨15227307605397966322552145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10151538403598644215034763 15227307605397966322552145)
                  ·
                    refine ⟨11420480704048474741914109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15227307605397966322552145 11420480704048474741914109)
                    ·
                      refine ⟨4282680264018178028217791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11420480704048474741914109 4282680264018178028217791)
                      ·
                        rfl

theorem cell23_8340490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_8340490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340490 prefixEnd_8340490 := by exact prefixLift 8340490
  have htrace : WordTrace (prefixWord ++ tailWord_8340490) baseStart_8340490 baseEnd_8340490 := by
    simpa [prefixWord, tailWord_8340490, baseEnd_8340490] using wordTrace_append hprefix tailTrace_8340490
  have hstable : (prefixWord ++ tailWord_8340490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340490).length < 2 ^ (prefixWord ++ tailWord_8340490).sum := by decide
  have hdescent : baseEnd_8340490 < baseStart_8340490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340496 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 7, 3, 2]
def baseStart_8340496 : Nat := 118140960795 + 8340496 * 2 ^ 59
def prefixEnd_8340496 : Nat := 4983230072969 + 3 ^ 40 * 8340496 * 2
def baseEnd_8340496 : Nat := 4282683344902105004742763

theorem tailTrace_8340496 : CollatzResearch.WordTrace tailWord_8340496 prefixEnd_8340496 4282683344902105004742763 := by
  unfold tailWord_8340496
  simp only [CollatzResearch.WordTrace]
  refine ⟨152101440195907455078092671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202801920261209940104123561 152101440195907455078092671)
  ·
    refine ⟨228152160293861182617139007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152101440195907455078092671 228152160293861182617139007)
    ·
      refine ⟨342228240440791773925708511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228152160293861182617139007 342228240440791773925708511)
      ·
        refine ⟨513342360661187660888562767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342228240440791773925708511 513342360661187660888562767)
        ·
          refine ⟨770013540991781491332844151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513342360661187660888562767 770013540991781491332844151)
          ·
            refine ⟨1155020311487672236999266227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770013540991781491332844151 1155020311487672236999266227)
            ·
              refine ⟨1732530467231508355498899341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155020311487672236999266227 1732530467231508355498899341)
              ·
                refine ⟨649698925211815633312087253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1732530467231508355498899341 649698925211815633312087253)
                ·
                  refine ⟨15227318559651928905752045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 649698925211815633312087253 15227318559651928905752045)
                  ·
                    refine ⟨5710244459869473339657017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15227318559651928905752045 5710244459869473339657017)
                    ·
                      refine ⟨4282683344902105004742763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5710244459869473339657017 4282683344902105004742763)
                      ·
                        rfl

theorem cell23_8340496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7, 3, 2].length) (baseStart_8340496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340496 prefixEnd_8340496 := by exact prefixLift 8340496
  have htrace : WordTrace (prefixWord ++ tailWord_8340496) baseStart_8340496 baseEnd_8340496 := by
    simpa [prefixWord, tailWord_8340496, baseEnd_8340496] using wordTrace_append hprefix tailTrace_8340496
  have hstable : (prefixWord ++ tailWord_8340496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340496).length < 2 ^ (prefixWord ++ tailWord_8340496).sum := by decide
  have hdescent : baseEnd_8340496 < baseStart_8340496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340498 : List Nat := [3, 2, 5, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_8340498 : Nat := 118140960795 + 8340498 * 2 ^ 59
def prefixEnd_8340498 : Nat := 4983230072969 + 3 ^ 40 * 8340498 * 2
def baseEnd_8340498 : Nat := 4282684371863413996917755

theorem tailTrace_8340498 : CollatzResearch.WordTrace tailWord_8340498 prefixEnd_8340498 4282684371863413996917755 := by
  unfold tailWord_8340498
  simp only [CollatzResearch.WordTrace]
  refine ⟨76050738334451916124439537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202801968891871776331838765 76050738334451916124439537)
  ·
    refine ⟨57038053750838937093329653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76050738334451916124439537 57038053750838937093329653)
    ·
      refine ⟨5347317539141150352499655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57038053750838937093329653 5347317539141150352499655)
      ·
        refine ⟨8020976308711725528749483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5347317539141150352499655 8020976308711725528749483)
        ·
          refine ⟨12031464463067588293124225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8020976308711725528749483 12031464463067588293124225)
          ·
            refine ⟨9023598347300691219843169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12031464463067588293124225 9023598347300691219843169)
            ·
              refine ⟨6767698760475518414882377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9023598347300691219843169 6767698760475518414882377)
              ·
                refine ⟨5075774070356638811161783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6767698760475518414882377 5075774070356638811161783)
                ·
                  refine ⟨7613661105534958216742675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075774070356638811161783 7613661105534958216742675)
                  ·
                    refine ⟨11420491658302437325114013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7613661105534958216742675 11420491658302437325114013)
                    ·
                      refine ⟨4282684371863413996917755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11420491658302437325114013 4282684371863413996917755)
                      ·
                        rfl

theorem cell23_8340498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_8340498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340498 prefixEnd_8340498 := by exact prefixLift 8340498
  have htrace : WordTrace (prefixWord ++ tailWord_8340498) baseStart_8340498 baseEnd_8340498 := by
    simpa [prefixWord, tailWord_8340498, baseEnd_8340498] using wordTrace_append hprefix tailTrace_8340498
  have hstable : (prefixWord ++ tailWord_8340498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340498).length < 2 ^ (prefixWord ++ tailWord_8340498).sum := by decide
  have hdescent : baseEnd_8340498 < baseStart_8340498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340504 : List Nat := [2, 1, 2, 3, 2, 4, 2, 2, 1, 2, 2]
def baseStart_8340504 : Nat := 118140960795 + 8340504 * 2 ^ 59
def prefixEnd_8340504 : Nat := 4983230072969 + 3 ^ 40 * 8340504 * 2
def baseEnd_8340504 : Nat := 4282687452747340973442727

theorem tailTrace_8340504 : CollatzResearch.WordTrace tailWord_8340504 prefixEnd_8340504 4282687452747340973442727 := by
  unfold tailWord_8340504
  simp only [CollatzResearch.WordTrace]
  refine ⟨152101586087892963761238283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202802114783857285014984377 152101586087892963761238283)
  ·
    refine ⟨228152379131839445641857425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152101586087892963761238283 228152379131839445641857425)
    ·
      refine ⟨171114284348879584231393069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228152379131839445641857425 171114284348879584231393069)
      ·
        refine ⟨64167856630829844086772401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171114284348879584231393069 64167856630829844086772401)
        ·
          refine ⟨48125892473122383065079301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64167856630829844086772401 48125892473122383065079301)
          ·
            refine ⟨9023604838710446824702369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48125892473122383065079301 9023604838710446824702369)
            ·
              refine ⟨6767703629032835118526777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9023604838710446824702369 6767703629032835118526777)
              ·
                refine ⟨5075777721774626338895083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6767703629032835118526777 5075777721774626338895083)
                ·
                  refine ⟨7613666582661939508342625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075777721774626338895083 7613666582661939508342625)
                  ·
                    refine ⟨5710249936996454631256969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7613666582661939508342625 5710249936996454631256969)
                    ·
                      refine ⟨4282687452747340973442727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5710249936996454631256969 4282687452747340973442727)
                      ·
                        rfl

theorem cell23_8340504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_8340504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340504 prefixEnd_8340504 := by exact prefixLift 8340504
  have htrace : WordTrace (prefixWord ++ tailWord_8340504) baseStart_8340504 baseEnd_8340504 := by
    simpa [prefixWord, tailWord_8340504, baseEnd_8340504] using wordTrace_append hprefix tailTrace_8340504
  have hstable : (prefixWord ++ tailWord_8340504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340504).length < 2 ^ (prefixWord ++ tailWord_8340504).sum := by decide
  have hdescent : baseEnd_8340504 < baseStart_8340504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340513 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 3, 3, 2]
def baseStart_8340513 : Nat := 118140960795 + 8340513 * 2 ^ 59
def prefixEnd_8340513 : Nat := 4983230072969 + 3 ^ 40 * 8340513 * 2
def baseEnd_8340513 : Nat := 4282692074073231438230185

theorem tailTrace_8340513 : CollatzResearch.WordTrace tailWord_8340513 prefixEnd_8340513 4282692074073231438230185 := by
  unfold tailWord_8340513
  simp only [CollatzResearch.WordTrace]
  refine ⟨304203500432753322059554193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202802333621835548039702795 304203500432753322059554193)
  ·
    refine ⟨228152625324564991544665645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304203500432753322059554193 228152625324564991544665645)
    ·
      refine ⟨85557234496711871829249617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228152625324564991544665645 85557234496711871829249617)
      ·
        refine ⟨64167925872533903871937213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85557234496711871829249617 64167925872533903871937213)
        ·
          refine ⟨24062972202200213951976455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64167925872533903871937213 24062972202200213951976455)
          ·
            refine ⟨36094458303300320927964683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24062972202200213951976455 36094458303300320927964683)
            ·
              refine ⟨54141687454950481391947025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36094458303300320927964683 54141687454950481391947025)
              ·
                refine ⟨40606265591212861043960269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54141687454950481391947025 40606265591212861043960269)
                ·
                  refine ⟨15227349596704822891485101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40606265591212861043960269 15227349596704822891485101)
                  ·
                    refine ⟨5710256098764308584306913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15227349596704822891485101 5710256098764308584306913)
                    ·
                      refine ⟨4282692074073231438230185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5710256098764308584306913 4282692074073231438230185)
                      ·
                        rfl

theorem cell23_8340513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_8340513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340513 prefixEnd_8340513 := by exact prefixLift 8340513
  have htrace : WordTrace (prefixWord ++ tailWord_8340513) baseStart_8340513 baseEnd_8340513 := by
    simpa [prefixWord, tailWord_8340513, baseEnd_8340513] using wordTrace_append hprefix tailTrace_8340513
  have hstable : (prefixWord ++ tailWord_8340513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340513).length < 2 ^ (prefixWord ++ tailWord_8340513).sum := by decide
  have hdescent : baseEnd_8340513 < baseStart_8340513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340526 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_8340526 : Nat := 118140960795 + 8340526 * 2 ^ 59
def prefixEnd_8340526 : Nat := 4983230072969 + 3 ^ 40 * 8340526 * 2
def baseEnd_8340526 : Nat := 4282698749321739887367625

theorem tailTrace_8340526 : CollatzResearch.WordTrace tailWord_8340526 prefixEnd_8340526 4282698749321739887367625 := by
  unfold tailWord_8340526
  simp only [CollatzResearch.WordTrace]
  refine ⟨38025496822713278159972179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202802649721137483519851621 38025496822713278159972179)
  ·
    refine ⟨57038245234069917239958269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38025496822713278159972179 57038245234069917239958269)
    ·
      refine ⟨21389341962776218964984351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57038245234069917239958269 21389341962776218964984351)
      ·
        refine ⟨32084012944164328447476527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21389341962776218964984351 32084012944164328447476527)
        ·
          refine ⟨48126019416246492671214791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32084012944164328447476527 48126019416246492671214791)
          ·
            refine ⟨72189029124369739006822187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48126019416246492671214791 72189029124369739006822187)
            ·
              refine ⟨108283543686554608510233281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72189029124369739006822187 108283543686554608510233281)
              ·
                refine ⟨81212657764915956382674961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108283543686554608510233281 81212657764915956382674961)
                ·
                  refine ⟨60909493323686967287006221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81212657764915956382674961 60909493323686967287006221)
                  ·
                    refine ⟨22841059996382612732627333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60909493323686967287006221 22841059996382612732627333)
                    ·
                      refine ⟨4282698749321739887367625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22841059996382612732627333 4282698749321739887367625)
                      ·
                        rfl

theorem cell23_8340526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_8340526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340526 prefixEnd_8340526 := by exact prefixLift 8340526
  have htrace : WordTrace (prefixWord ++ tailWord_8340526) baseStart_8340526 baseEnd_8340526 := by
    simpa [prefixWord, tailWord_8340526, baseEnd_8340526] using wordTrace_append hprefix tailTrace_8340526
  have hstable : (prefixWord ++ tailWord_8340526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340526).length < 2 ^ (prefixWord ++ tailWord_8340526).sum := by decide
  have hdescent : baseEnd_8340526 < baseStart_8340526 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340539 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 4]
def baseStart_8340539 : Nat := 118140960795 + 8340539 * 2 ^ 59
def prefixEnd_8340539 : Nat := 4983230072969 + 3 ^ 40 * 8340539 * 2
def baseEnd_8340539 : Nat := 4282705424570248336505065

theorem tailTrace_8340539 : CollatzResearch.WordTrace tailWord_8340539 prefixEnd_8340539 4282705424570248336505065 := by
  unfold tailWord_8340539
  simp only [CollatzResearch.WordTrace]
  refine ⟨304204448730659128500000671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202802965820439419000000447 304204448730659128500000671)
  ·
    refine ⟨456306673095988692750001007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304204448730659128500000671 456306673095988692750001007)
    ·
      refine ⟨684460009643983039125001511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456306673095988692750001007 684460009643983039125001511)
      ·
        refine ⟨1026690014465974558687502267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684460009643983039125001511 1026690014465974558687502267)
        ·
          refine ⟨1540035021698961838031253401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026690014465974558687502267 1540035021698961838031253401)
          ·
            refine ⟨1155026266274221378523440051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1540035021698961838031253401 1155026266274221378523440051)
            ·
              refine ⟨1732539399411332067785160077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155026266274221378523440051 1732539399411332067785160077)
              ·
                refine ⟨649702274779249525419435029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1732539399411332067785160077 649702274779249525419435029)
                ·
                  refine ⟨30454794130277321504036017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 649702274779249525419435029 30454794130277321504036017)
                  ·
                    refine ⟨22841095597707991128027013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30454794130277321504036017 22841095597707991128027013)
                    ·
                      refine ⟨4282705424570248336505065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22841095597707991128027013 4282705424570248336505065)
                      ·
                        rfl

theorem cell23_8340539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 4].length) (baseStart_8340539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340539 prefixEnd_8340539 := by exact prefixLift 8340539
  have htrace : WordTrace (prefixWord ++ tailWord_8340539) baseStart_8340539 baseEnd_8340539 := by
    simpa [prefixWord, tailWord_8340539, baseEnd_8340539] using wordTrace_append hprefix tailTrace_8340539
  have hstable : (prefixWord ++ tailWord_8340539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340539).length < 2 ^ (prefixWord ++ tailWord_8340539).sum := by decide
  have hdescent : baseEnd_8340539 < baseStart_8340539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340543 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 4, 2, 2]
def baseStart_8340543 : Nat := 118140960795 + 8340543 * 2 ^ 59
def prefixEnd_8340543 : Nat := 4983230072969 + 3 ^ 40 * 8340543 * 2
def baseEnd_8340543 : Nat := 4282707478492866320855047

theorem tailTrace_8340543 : CollatzResearch.WordTrace tailWord_8340543 prefixEnd_8340543 4282707478492866320855047 := by
  unfold tailWord_8340543
  simp only [CollatzResearch.WordTrace]
  refine ⟨304204594622644637183146283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202803063081763091455430855 304204594622644637183146283)
  ·
    refine ⟨456306891933966955774719425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304204594622644637183146283 456306891933966955774719425)
    ·
      refine ⟨342230168950475216831039569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456306891933966955774719425 342230168950475216831039569)
      ·
        refine ⟨256672626712856412623279677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342230168950475216831039569 256672626712856412623279677)
        ·
          refine ⟨96252235017321154733729879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256672626712856412623279677 96252235017321154733729879)
          ·
            refine ⟨144378352525981732100594819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96252235017321154733729879 144378352525981732100594819)
            ·
              refine ⟨216567528788972598150892229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144378352525981732100594819 216567528788972598150892229)
              ·
                refine ⟨40606411647932362153292293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216567528788972598150892229 40606411647932362153292293)
                ·
                  refine ⟨7613702183987317903742305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40606411647932362153292293 7613702183987317903742305)
                  ·
                    refine ⟨5710276637990488427806729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7613702183987317903742305 5710276637990488427806729)
                    ·
                      refine ⟨4282707478492866320855047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5710276637990488427806729 4282707478492866320855047)
                      ·
                        rfl

theorem cell23_8340543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 2, 2].length) (baseStart_8340543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340543 prefixEnd_8340543 := by exact prefixLift 8340543
  have htrace : WordTrace (prefixWord ++ tailWord_8340543) baseStart_8340543 baseEnd_8340543 := by
    simpa [prefixWord, tailWord_8340543, baseEnd_8340543] using wordTrace_append hprefix tailTrace_8340543
  have hstable : (prefixWord ++ tailWord_8340543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340543).length < 2 ^ (prefixWord ++ tailWord_8340543).sum := by decide
  have hdescent : baseEnd_8340543 < baseStart_8340543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340576 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 3]
def baseStart_8340576 : Nat := 118140960795 + 8340576 * 2 ^ 59
def prefixEnd_8340576 : Nat := 4983230072969 + 3 ^ 40 * 8340576 * 2
def baseEnd_8340576 : Nat := 4282724423354464691742395

theorem tailTrace_8340576 : CollatzResearch.WordTrace tailWord_8340576 prefixEnd_8340576 4282724423354464691742395 := by
  unfold tailWord_8340576
  simp only [CollatzResearch.WordTrace]
  refine ⟨152102899115762541909548791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202803865487683389212731721 152102899115762541909548791)
  ·
    refine ⟨228154348673643812864323187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152102899115762541909548791 228154348673643812864323187)
    ·
      refine ⟨342231523010465719296484781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228154348673643812864323187 342231523010465719296484781)
      ·
        refine ⟨128336821128924644736181793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342231523010465719296484781 128336821128924644736181793)
        ·
          refine ⟨96252615846693483552136345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128336821128924644736181793 96252615846693483552136345)
          ·
            refine ⟨72189461885020112664102259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96252615846693483552136345 72189461885020112664102259)
            ·
              refine ⟨108284192827530168996153389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72189461885020112664102259 108284192827530168996153389)
              ·
                refine ⟨40606572310323813373557521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108284192827530168996153389 40606572310323813373557521)
                ·
                  refine ⟨30454929232742860030168141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40606572310323813373557521 30454929232742860030168141)
                  ·
                    refine ⟨11420598462278572511313053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30454929232742860030168141 11420598462278572511313053)
                    ·
                      refine ⟨4282724423354464691742395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11420598462278572511313053 4282724423354464691742395)
                      ·
                        rfl

theorem cell23_8340576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_8340576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340576 prefixEnd_8340576 := by exact prefixLift 8340576
  have htrace : WordTrace (prefixWord ++ tailWord_8340576) baseStart_8340576 baseEnd_8340576 := by
    simpa [prefixWord, tailWord_8340576, baseEnd_8340576] using wordTrace_append hprefix tailTrace_8340576
  have hstable : (prefixWord ++ tailWord_8340576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340576).length < 2 ^ (prefixWord ++ tailWord_8340576).sum := by decide
  have hdescent : baseEnd_8340576 < baseStart_8340576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340613 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 2, 5]
def baseStart_8340613 : Nat := 118140960795 + 8340613 * 2 ^ 59
def prefixEnd_8340613 : Nat := 4983230072969 + 3 ^ 40 * 8340613 * 2
def baseEnd_8340613 : Nat := 1427581140712893682326575

theorem tailTrace_8340613 : CollatzResearch.WordTrace tailWord_8340613 prefixEnd_8340613 1427581140712893682326575 := by
  unfold tailWord_8340613
  simp only [CollatzResearch.WordTrace]
  refine ⟨304207147732391039138194493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202804765154927359425462995 304207147732391039138194493)
  ·
    refine ⟨114077680399646639676822935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304207147732391039138194493 114077680399646639676822935)
    ·
      refine ⟨171116520599469959515234403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114077680399646639676822935 171116520599469959515234403)
      ·
        refine ⟨256674780899204939272851605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171116520599469959515234403 256674780899204939272851605)
        ·
          refine ⟨12031630354650231528414919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 256674780899204939272851605 12031630354650231528414919)
          ·
            refine ⟨18047445531975347292622379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12031630354650231528414919 18047445531975347292622379)
            ·
              refine ⟨27071168297963020938933569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18047445531975347292622379 27071168297963020938933569)
              ·
                refine ⟨20303376223472265704200177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27071168297963020938933569 20303376223472265704200177)
                ·
                  refine ⟨15227532167604199278150133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20303376223472265704200177 15227532167604199278150133)
                  ·
                    refine ⟨1427581140712893682326575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15227532167604199278150133 1427581140712893682326575)
                    ·
                      rfl

theorem cell23_8340613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_8340613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340613 prefixEnd_8340613 := by exact prefixLift 8340613
  have htrace : WordTrace (prefixWord ++ tailWord_8340613) baseStart_8340613 baseEnd_8340613 := by
    simpa [prefixWord, tailWord_8340613, baseEnd_8340613] using wordTrace_append hprefix tailTrace_8340613
  have hstable : (prefixWord ++ tailWord_8340613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340613).length < 2 ^ (prefixWord ++ tailWord_8340613).sum := by decide
  have hdescent : baseEnd_8340613 < baseStart_8340613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340650 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_8340650 : Nat := 118140960795 + 8340650 * 2 ^ 59
def prefixEnd_8340650 : Nat := 4983230072969 + 3 ^ 40 * 8340650 * 2
def baseEnd_8340650 : Nat := 4282762420922897402217055

theorem tailTrace_8340650 : CollatzResearch.WordTrace tailWord_8340650 prefixEnd_8340650 4282762420922897402217055 := by
  unfold tailWord_8340650
  simp only [CollatzResearch.WordTrace]
  refine ⟨76052124308314248614322851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202805664822171329638194269 76052124308314248614322851)
  ·
    refine ⟨114078186462471372921484277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76052124308314248614322851 114078186462471372921484277)
    ·
      refine ⟨10694829980856691211389151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114078186462471372921484277 10694829980856691211389151)
      ·
        refine ⟨16042244971285036817083727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10694829980856691211389151 16042244971285036817083727)
        ·
          refine ⟨24063367456927555225625591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16042244971285036817083727 24063367456927555225625591)
          ·
            refine ⟨36095051185391332838438387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24063367456927555225625591 36095051185391332838438387)
            ·
              refine ⟨54142576778086999257657581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36095051185391332838438387 54142576778086999257657581)
              ·
                refine ⟨20303466291782624721621593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54142576778086999257657581 20303466291782624721621593)
                ·
                  refine ⟨15227599718836968541216195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20303466291782624721621593 15227599718836968541216195)
                  ·
                    refine ⟨22841399578255452811824293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15227599718836968541216195 22841399578255452811824293)
                    ·
                      refine ⟨4282762420922897402217055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22841399578255452811824293 4282762420922897402217055)
                      ·
                        rfl

theorem cell23_8340650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_8340650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340650 prefixEnd_8340650 := by exact prefixLift 8340650
  have htrace : WordTrace (prefixWord ++ tailWord_8340650) baseStart_8340650 baseEnd_8340650 := by
    simpa [prefixWord, tailWord_8340650, baseEnd_8340650] using wordTrace_append hprefix tailTrace_8340650
  have hstable : (prefixWord ++ tailWord_8340650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340650).length < 2 ^ (prefixWord ++ tailWord_8340650).sum := by decide
  have hdescent : baseEnd_8340650 < baseStart_8340650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340670 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_8340670 : Nat := 118140960795 + 8340670 * 2 ^ 59
def prefixEnd_8340670 : Nat := 4983230072969 + 3 ^ 40 * 8340670 * 2
def baseEnd_8340670 : Nat := 4282772690535987323966963

theorem tailTrace_8340670 : CollatzResearch.WordTrace tailWord_8340670 prefixEnd_8340670 4282772690535987323966963 := by
  unfold tailWord_8340670
  simp only [CollatzResearch.WordTrace]
  refine ⟨38026153336648067234127433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202806151128789691915346309 38026153336648067234127433)
  ·
    refine ⟨28519615002486050425595575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38026153336648067234127433 28519615002486050425595575)
    ·
      refine ⟨42779422503729075638393363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28519615002486050425595575 42779422503729075638393363)
      ·
        refine ⟨64169133755593613457590045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42779422503729075638393363 64169133755593613457590045)
        ·
          refine ⟨24063425158347605046596267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64169133755593613457590045 24063425158347605046596267)
          ·
            refine ⟨36095137737521407569894401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24063425158347605046596267 36095137737521407569894401)
            ·
              refine ⟨27071353303141055677420801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36095137737521407569894401 27071353303141055677420801)
              ·
                refine ⟨20303514977355791758065601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27071353303141055677420801 20303514977355791758065601)
                ·
                  refine ⟨15227636233016843818549201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20303514977355791758065601 15227636233016843818549201)
                  ·
                    refine ⟨11420727174762632863911901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15227636233016843818549201 11420727174762632863911901)
                    ·
                      refine ⟨4282772690535987323966963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11420727174762632863911901 4282772690535987323966963)
                      ·
                        rfl

theorem cell23_8340670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_8340670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340670 prefixEnd_8340670 := by exact prefixLift 8340670
  have htrace : WordTrace (prefixWord ++ tailWord_8340670) baseStart_8340670 baseEnd_8340670 := by
    simpa [prefixWord, tailWord_8340670, baseEnd_8340670] using wordTrace_append hprefix tailTrace_8340670
  have hstable : (prefixWord ++ tailWord_8340670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340670).length < 2 ^ (prefixWord ++ tailWord_8340670).sum := by decide
  have hdescent : baseEnd_8340670 < baseStart_8340670 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340734 : List Nat := [4, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_8340734 : Nat := 118140960795 + 8340734 * 2 ^ 59
def prefixEnd_8340734 : Nat := 4983230072969 + 3 ^ 40 * 8340734 * 2
def baseEnd_8340734 : Nat := 4282805553297875073566669

theorem tailTrace_8340734 : CollatzResearch.WordTrace tailWord_8340734 prefixEnd_8340734 4282805553297875073566669 := by
  unfold tailWord_8340734
  simp only [CollatzResearch.WordTrace]
  refine ⟨38026445120619084600418657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202807707309968451202232837 38026445120619084600418657)
  ·
    refine ⟨28519833840464313450313993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38026445120619084600418657 28519833840464313450313993)
    ·
      refine ⟨21389875380348235087735495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28519833840464313450313993 21389875380348235087735495)
      ·
        refine ⟨32084813070522352631603243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21389875380348235087735495 32084813070522352631603243)
        ·
          refine ⟨48127219605783528947404865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32084813070522352631603243 48127219605783528947404865)
          ·
            refine ⟨36095414704337646710553649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48127219605783528947404865 36095414704337646710553649)
            ·
              refine ⟨27071561028253235032915237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36095414704337646710553649 27071561028253235032915237)
              ·
                refine ⟨5075917692797481568671607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27071561028253235032915237 5075917692797481568671607)
                ·
                  refine ⟨7613876539196222353007411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075917692797481568671607 7613876539196222353007411)
                  ·
                    refine ⟨11420814808794333529511117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7613876539196222353007411 11420814808794333529511117)
                    ·
                      refine ⟨4282805553297875073566669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11420814808794333529511117 4282805553297875073566669)
                      ·
                        rfl

theorem cell23_8340734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_8340734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340734 prefixEnd_8340734 := by exact prefixLift 8340734
  have htrace : WordTrace (prefixWord ++ tailWord_8340734) baseStart_8340734 baseEnd_8340734 := by
    simpa [prefixWord, tailWord_8340734, baseEnd_8340734] using wordTrace_append hprefix tailTrace_8340734
  have hstable : (prefixWord ++ tailWord_8340734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340734).length < 2 ^ (prefixWord ++ tailWord_8340734).sum := by decide
  have hdescent : baseEnd_8340734 < baseStart_8340734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340736 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 6]
def baseStart_8340736 : Nat := 118140960795 + 8340736 * 2 ^ 59
def prefixEnd_8340736 : Nat := 4983230072969 + 3 ^ 40 * 8340736 * 2
def baseEnd_8340736 : Nat := 4282806580259184065741659

theorem tailTrace_8340736 : CollatzResearch.WordTrace tailWord_8340736 prefixEnd_8340736 4282806580259184065741659 := by
  unfold tailWord_8340736
  simp only [CollatzResearch.WordTrace]
  refine ⟨152105816955472715572461031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202807755940630287429948041 152105816955472715572461031)
  ·
    refine ⟨228158725433209073358691547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152105816955472715572461031 228158725433209073358691547)
    ·
      refine ⟨342238088149813610038037321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228158725433209073358691547 342238088149813610038037321)
      ·
        refine ⟨256678566112360207528527991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342238088149813610038037321 256678566112360207528527991)
        ·
          refine ⟨385017849168540311292791987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256678566112360207528527991 385017849168540311292791987)
          ·
            refine ⟨577526773752810466939187981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385017849168540311292791987 577526773752810466939187981)
            ·
              refine ⟨216572540157303925102195493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 577526773752810466939187981 216572540157303925102195493)
              ·
                refine ⟨40607351279494485956661655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216572540157303925102195493 40607351279494485956661655)
                ·
                  refine ⟨60911026919241728934992483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40607351279494485956661655 60911026919241728934992483)
                  ·
                    refine ⟨91366540378862593402488725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60911026919241728934992483 91366540378862593402488725)
                    ·
                      refine ⟨4282806580259184065741659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91366540378862593402488725 4282806580259184065741659)
                      ·
                        rfl

theorem cell23_8340736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_8340736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340736 prefixEnd_8340736 := by exact prefixLift 8340736
  have htrace : WordTrace (prefixWord ++ tailWord_8340736) baseStart_8340736 baseEnd_8340736 := by
    simpa [prefixWord, tailWord_8340736, baseEnd_8340736] using wordTrace_append hprefix tailTrace_8340736
  have hstable : (prefixWord ++ tailWord_8340736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340736).length < 2 ^ (prefixWord ++ tailWord_8340736).sum := by decide
  have hdescent : baseEnd_8340736 < baseStart_8340736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340746 : List Nat := [3, 1, 2, 2, 1, 1, 1, 12]
def baseStart_8340746 : Nat := 118140960795 + 8340746 * 2 ^ 59
def prefixEnd_8340746 : Nat := 4983230072969 + 3 ^ 40 * 8340746 * 2
def baseEnd_8340746 : Nat := 158622656113545519504319

theorem tailTrace_8340746 : CollatzResearch.WordTrace tailWord_8340746 prefixEnd_8340746 158622656113545519504319 := by
  unfold tailWord_8340746
  simp only [CollatzResearch.WordTrace]
  refine ⟨76052999660227300713196523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202807999093939468568524061 76052999660227300713196523)
  ·
    refine ⟨114079499490340951069794785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76052999660227300713196523 114079499490340951069794785)
    ·
      refine ⟨85559624617755713302346089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114079499490340951069794785 85559624617755713302346089)
      ·
        refine ⟨64169718463316784976759567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85559624617755713302346089 64169718463316784976759567)
        ·
          refine ⟨96254577694975177465139351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64169718463316784976759567 96254577694975177465139351)
          ·
            refine ⟨144381866542462766197709027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96254577694975177465139351 144381866542462766197709027)
            ·
              refine ⟨216572799813694149296563541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144381866542462766197709027 216572799813694149296563541)
              ·
                refine ⟨158622656113545519504319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 216572799813694149296563541 158622656113545519504319)
                ·
                  rfl

theorem cell23_8340746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 12].length) (baseStart_8340746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340746 prefixEnd_8340746 := by exact prefixLift 8340746
  have htrace : WordTrace (prefixWord ++ tailWord_8340746) baseStart_8340746 baseEnd_8340746 := by
    simpa [prefixWord, tailWord_8340746, baseEnd_8340746] using wordTrace_append hprefix tailTrace_8340746
  have hstable : (prefixWord ++ tailWord_8340746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340746).length < 2 ^ (prefixWord ++ tailWord_8340746).sum := by decide
  have hdescent : baseEnd_8340746 < baseStart_8340746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340750 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_8340750 : Nat := 118140960795 + 8340750 * 2 ^ 59
def prefixEnd_8340750 : Nat := 4983230072969 + 3 ^ 40 * 8340750 * 2
def baseEnd_8340750 : Nat := 1427604589662782336988865

theorem tailTrace_8340750 : CollatzResearch.WordTrace tailWord_8340750 prefixEnd_8340750 1427604589662782336988865 := by
  unfold tailWord_8340750
  simp only [CollatzResearch.WordTrace]
  refine ⟨38026518066611838941991463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202808096355263141023954469 38026518066611838941991463)
  ·
    refine ⟨57039777099917758412987195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38026518066611838941991463 57039777099917758412987195)
    ·
      refine ⟨85559665649876637619480793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57039777099917758412987195 85559665649876637619480793)
      ·
        refine ⟨64169749237407478214610595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85559665649876637619480793 64169749237407478214610595)
        ·
          refine ⟨96254623856111217321915893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64169749237407478214610595 96254623856111217321915893)
          ·
            refine ⟨9023870986510426623929615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96254623856111217321915893 9023870986510426623929615)
            ·
              refine ⟨13535806479765639935894423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9023870986510426623929615 13535806479765639935894423)
              ·
                refine ⟨20303709719648459903841635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13535806479765639935894423 20303709719648459903841635)
                ·
                  refine ⟨30455564579472689855762453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20303709719648459903841635 30455564579472689855762453)
                  ·
                    refine ⟨1427604589662782336988865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30455564579472689855762453 1427604589662782336988865)
                    ·
                      rfl

theorem cell23_8340750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_8340750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340750 prefixEnd_8340750 := by exact prefixLift 8340750
  have htrace : WordTrace (prefixWord ++ tailWord_8340750) baseStart_8340750 baseEnd_8340750 := by
    simpa [prefixWord, tailWord_8340750, baseEnd_8340750] using wordTrace_append hprefix tailTrace_8340750
  have hstable : (prefixWord ++ tailWord_8340750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340750).length < 2 ^ (prefixWord ++ tailWord_8340750).sum := by decide
  have hdescent : baseEnd_8340750 < baseStart_8340750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340754 : List Nat := [3, 2, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_8340754 : Nat := 118140960795 + 8340754 * 2 ^ 59
def prefixEnd_8340754 : Nat := 4983230072969 + 3 ^ 40 * 8340754 * 2
def baseEnd_8340754 : Nat := 1427605274303654998438859

theorem tailTrace_8340754 : CollatzResearch.WordTrace tailWord_8340754 prefixEnd_8340754 1427605274303654998438859 := by
  unfold tailWord_8340754
  simp only [CollatzResearch.WordTrace]
  refine ⟨76053072606220055054769329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202808193616586813479384877 76053072606220055054769329)
  ·
    refine ⟨57039804454665041291076997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76053072606220055054769329 57039804454665041291076997)
    ·
      refine ⟨10694963335249695242076937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57039804454665041291076997 10694963335249695242076937)
      ·
        refine ⟨8021222501437271431557703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10694963335249695242076937 8021222501437271431557703)
        ·
          refine ⟨12031833752155907147336555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8021222501437271431557703 12031833752155907147336555)
          ·
            refine ⟨18047750628233860721004833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12031833752155907147336555 18047750628233860721004833)
            ·
              refine ⟨13535812971175395540753625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18047750628233860721004833 13535812971175395540753625)
              ·
                refine ⟨10151859728381546655565219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13535812971175395540753625 10151859728381546655565219)
                ·
                  refine ⟨15227789592572319983347829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10151859728381546655565219 15227789592572319983347829)
                  ·
                    refine ⟨1427605274303654998438859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15227789592572319983347829 1427605274303654998438859)
                    ·
                      rfl

theorem cell23_8340754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_8340754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340754 prefixEnd_8340754 := by exact prefixLift 8340754
  have htrace : WordTrace (prefixWord ++ tailWord_8340754) baseStart_8340754 baseEnd_8340754 := by
    simpa [prefixWord, tailWord_8340754, baseEnd_8340754] using wordTrace_append hprefix tailTrace_8340754
  have hstable : (prefixWord ++ tailWord_8340754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340754).length < 2 ^ (prefixWord ++ tailWord_8340754).sum := by decide
  have hdescent : baseEnd_8340754 < baseStart_8340754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340760 : List Nat := [2, 1, 2, 3, 1, 3, 1, 4, 1, 2, 3]
def baseStart_8340760 : Nat := 118140960795 + 8340760 * 2 ^ 59
def prefixEnd_8340760 : Nat := 4983230072969 + 3 ^ 40 * 8340760 * 2
def baseEnd_8340760 : Nat := 4282818903794891971841549

theorem tailTrace_8340760 : CollatzResearch.WordTrace tailWord_8340760 prefixEnd_8340760 4282818903794891971841549 := by
  unfold tailWord_8340760
  simp only [CollatzResearch.WordTrace]
  refine ⟨152106254631429241621897867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202808339508572322162530489 152106254631429241621897867)
  ·
    refine ⟨228159381947143862432846801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152106254631429241621897867 228159381947143862432846801)
    ·
      refine ⟨171119536460357896824635101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228159381947143862432846801 171119536460357896824635101)
      ·
        refine ⟨64169826172634211309238163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171119536460357896824635101 64169826172634211309238163)
        ·
          refine ⟨96254739258951316963857245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64169826172634211309238163 96254739258951316963857245)
          ·
            refine ⟨36095527222106743861446467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96254739258951316963857245 36095527222106743861446467)
            ·
              refine ⟨54143290833160115792169701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36095527222106743861446467 54143290833160115792169701)
              ·
                refine ⟨10151867031217521711031819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54143290833160115792169701 10151867031217521711031819)
                ·
                  refine ⟨15227800546826282566547729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10151867031217521711031819 15227800546826282566547729)
                  ·
                    refine ⟨11420850410119711924910797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15227800546826282566547729 11420850410119711924910797)
                    ·
                      refine ⟨4282818903794891971841549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11420850410119711924910797 4282818903794891971841549)
                      ·
                        rfl

theorem cell23_8340760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_8340760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340760 prefixEnd_8340760 := by exact prefixLift 8340760
  have htrace : WordTrace (prefixWord ++ tailWord_8340760) baseStart_8340760 baseEnd_8340760 := by
    simpa [prefixWord, tailWord_8340760, baseEnd_8340760] using wordTrace_append hprefix tailTrace_8340760
  have hstable : (prefixWord ++ tailWord_8340760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340760).length < 2 ^ (prefixWord ++ tailWord_8340760).sum := by decide
  have hdescent : baseEnd_8340760 < baseStart_8340760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340800 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 3, 3, 2]
def baseStart_8340800 : Nat := 118140960795 + 8340800 * 2 ^ 59
def prefixEnd_8340800 : Nat := 4983230072969 + 3 ^ 40 * 8340800 * 2
def baseEnd_8340800 : Nat := 4282839443021071815341365

theorem tailTrace_8340800 : CollatzResearch.WordTrace tailWord_8340800 prefixEnd_8340800 4282839443021071815341365 := by
  unfold tailWord_8340800
  simp only [CollatzResearch.WordTrace]
  refine ⟨152106984091356785037625927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202809312121809046716834569 152106984091356785037625927)
  ·
    refine ⟨228160476137035177556438891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152106984091356785037625927 228160476137035177556438891)
    ·
      refine ⟨342240714205552766334658337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228160476137035177556438891 342240714205552766334658337)
      ·
        refine ⟨256680535654164574750993753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342240714205552766334658337 256680535654164574750993753)
        ·
          refine ⟨192510401740623431063245315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256680535654164574750993753 192510401740623431063245315)
          ·
            refine ⟨288765602610935146594867973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192510401740623431063245315 288765602610935146594867973)
            ·
              refine ⟨54143550489550339986537745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288765602610935146594867973 54143550489550339986537745)
              ·
                refine ⟨40607662867162754989903309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54143550489550339986537745 40607662867162754989903309)
                ·
                  refine ⟨15227873575186033121213741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40607662867162754989903309 15227873575186033121213741)
                  ·
                    refine ⟨5710452590694762420455153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15227873575186033121213741 5710452590694762420455153)
                    ·
                      refine ⟨4282839443021071815341365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5710452590694762420455153 4282839443021071815341365)
                      ·
                        rfl

theorem cell23_8340800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3, 3, 2].length) (baseStart_8340800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340800 prefixEnd_8340800 := by exact prefixLift 8340800
  have htrace : WordTrace (prefixWord ++ tailWord_8340800) baseStart_8340800 baseEnd_8340800 := by
    simpa [prefixWord, tailWord_8340800, baseEnd_8340800] using wordTrace_append hprefix tailTrace_8340800
  have hstable : (prefixWord ++ tailWord_8340800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340800).length < 2 ^ (prefixWord ++ tailWord_8340800).sum := by decide
  have hdescent : baseEnd_8340800 < baseStart_8340800 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340807 : List Nat := [1, 1, 4, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_8340807 : Nat := 118140960795 + 8340807 * 2 ^ 59
def prefixEnd_8340807 : Nat := 4983230072969 + 3 ^ 40 * 8340807 * 2
def baseEnd_8340807 : Nat := 4282843037385653287953833

theorem tailTrace_8340807 : CollatzResearch.WordTrace tailWord_8340807 prefixEnd_8340807 4282843037385653287953833 := by
  unfold tailWord_8340807
  simp only [CollatzResearch.WordTrace]
  refine ⟨304214223493688210270756675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202809482329125473513837783 304214223493688210270756675)
  ·
    refine ⟨456321335240532315406135013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304214223493688210270756675 456321335240532315406135013)
    ·
      refine ⟨85560250357599809138650315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456321335240532315406135013 85560250357599809138650315)
      ·
        refine ⟨128340375536399713707975473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85560250357599809138650315 128340375536399713707975473)
        ·
          refine ⟨96255281652299785280981605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128340375536399713707975473 96255281652299785280981605)
          ·
            refine ⟨18047865309806209740184051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96255281652299785280981605 18047865309806209740184051)
            ·
              refine ⟨27071797964709314610276077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18047865309806209740184051 27071797964709314610276077)
              ·
                refine ⟨10151924236765992978853529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27071797964709314610276077 10151924236765992978853529)
                ·
                  refine ⟨7613943177574494734140147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10151924236765992978853529 7613943177574494734140147)
                  ·
                    refine ⟨11420914766361742101210221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7613943177574494734140147 11420914766361742101210221)
                    ·
                      refine ⟨4282843037385653287953833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11420914766361742101210221 4282843037385653287953833)
                      ·
                        rfl

theorem cell23_8340807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_8340807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340807 prefixEnd_8340807 := by exact prefixLift 8340807
  have htrace : WordTrace (prefixWord ++ tailWord_8340807) baseStart_8340807 baseEnd_8340807 := by
    simpa [prefixWord, tailWord_8340807, baseEnd_8340807] using wordTrace_append hprefix tailTrace_8340807
  have hstable : (prefixWord ++ tailWord_8340807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340807).length < 2 ^ (prefixWord ++ tailWord_8340807).sum := by decide
  have hdescent : baseEnd_8340807 < baseStart_8340807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340833 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_8340833 : Nat := 118140960795 + 8340833 * 2 ^ 59
def prefixEnd_8340833 : Nat := 4983230072969 + 3 ^ 40 * 8340833 * 2
def baseEnd_8340833 : Nat := 4282856387882670186228713

theorem tailTrace_8340833 : CollatzResearch.WordTrace tailWord_8340833 prefixEnd_8340833 4282856387882670186228713 := by
  unfold tailWord_8340833
  simp only [CollatzResearch.WordTrace]
  refine ⟨304215171791594016711203153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202810114527729344474135435 304215171791594016711203153)
  ·
    refine ⟨228161378843695512533402365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304215171791594016711203153 228161378843695512533402365)
    ·
      refine ⟨85560517066385817200025887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228161378843695512533402365 85560517066385817200025887)
      ·
        refine ⟨128340775599578725800038831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85560517066385817200025887 128340775599578725800038831)
        ·
          refine ⟨192511163399368088700058247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128340775599578725800038831 192511163399368088700058247)
          ·
            refine ⟨288766745099052133050087371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192511163399368088700058247 288766745099052133050087371)
            ·
              refine ⟨433150117648578199575131057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288766745099052133050087371 433150117648578199575131057)
              ·
                refine ⟨324862588236433649681348293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433150117648578199575131057 324862588236433649681348293)
                ·
                  refine ⟨60911735294331309315252805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324862588236433649681348293 60911735294331309315252805)
                  ·
                    refine ⟨11420950367687120496609901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60911735294331309315252805 11420950367687120496609901)
                    ·
                      refine ⟨4282856387882670186228713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11420950367687120496609901 4282856387882670186228713)
                      ·
                        rfl

theorem cell23_8340833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_8340833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340833 prefixEnd_8340833 := by exact prefixLift 8340833
  have htrace : WordTrace (prefixWord ++ tailWord_8340833) baseStart_8340833 baseEnd_8340833 := by
    simpa [prefixWord, tailWord_8340833, baseEnd_8340833] using wordTrace_append hprefix tailTrace_8340833
  have hstable : (prefixWord ++ tailWord_8340833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340833).length < 2 ^ (prefixWord ++ tailWord_8340833).sum := by decide
  have hdescent : baseEnd_8340833 < baseStart_8340833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340943 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 8]
def baseStart_8340943 : Nat := 118140960795 + 8340943 * 2 ^ 59
def prefixEnd_8340943 : Nat := 4983230072969 + 3 ^ 40 * 8340943 * 2
def baseEnd_8340943 : Nat := 475879207861629417317023

theorem tailTrace_8340943 : CollatzResearch.WordTrace tailWord_8340943 prefixEnd_8340943 475879207861629417317023 := by
  unfold tailWord_8340943
  simp only [CollatzResearch.WordTrace]
  refine ⟨304219183821195505497707483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202812789214130336998471655 304219183821195505497707483)
  ·
    refine ⟨456328775731793258246561225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304219183821195505497707483 456328775731793258246561225)
    ·
      refine ⟨342246581798844943684920919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456328775731793258246561225 342246581798844943684920919)
      ·
        refine ⟨513369872698267415527381379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342246581798844943684920919 513369872698267415527381379)
        ·
          refine ⟨770054809047401123291072069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513369872698267415527381379 770054809047401123291072069)
          ·
            refine ⟨144385276696387710617076013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 770054809047401123291072069 144385276696387710617076013)
            ·
              refine ⟨54144478761145391481403505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144385276696387710617076013 54144478761145391481403505)
              ·
                refine ⟨40608359070859043611052629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54144478761145391481403505 40608359070859043611052629)
                ·
                  refine ⟨475879207861629417317023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40608359070859043611052629 475879207861629417317023)
                  ·
                    rfl

theorem cell23_8340943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 8].length) (baseStart_8340943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340943 prefixEnd_8340943 := by exact prefixLift 8340943
  have htrace : WordTrace (prefixWord ++ tailWord_8340943) baseStart_8340943 baseEnd_8340943 := by
    simpa [prefixWord, tailWord_8340943, baseEnd_8340943] using wordTrace_append hprefix tailTrace_8340943
  have hstable : (prefixWord ++ tailWord_8340943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340943).length < 2 ^ (prefixWord ++ tailWord_8340943).sum := by decide
  have hdescent : baseEnd_8340943 < baseStart_8340943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340957 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_8340957 : Nat := 118140960795 + 8340957 * 2 ^ 59
def prefixEnd_8340957 : Nat := 4983230072969 + 3 ^ 40 * 8340957 * 2
def baseEnd_8340957 : Nat := 4282920059483827701078143

theorem tailTrace_8340957 : CollatzResearch.WordTrace tailWord_8340957 prefixEnd_8340957 4282920059483827701078143 := by
  unfold tailWord_8340957
  simp only [CollatzResearch.WordTrace]
  refine ⟨304219694443144785888717125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202813129628763190592478083 304219694443144785888717125)
  ·
    refine ⟨57041192708089647354134461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304219694443144785888717125 57041192708089647354134461)
    ·
      refine ⟨21390447265533617757800423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57041192708089647354134461 21390447265533617757800423)
      ·
        refine ⟨32085670898300426636700635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21390447265533617757800423 32085670898300426636700635)
        ·
          refine ⟨48128506347450639955050953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32085670898300426636700635 48128506347450639955050953)
          ·
            refine ⟨36096379760587979966288215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48128506347450639955050953 36096379760587979966288215)
            ·
              refine ⟨54144569640881969949432323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36096379760587979966288215 54144569640881969949432323)
              ·
                refine ⟨81216854461322954924148485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54144569640881969949432323 81216854461322954924148485)
                ·
                  refine ⟨15228160211498054048277841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81216854461322954924148485 15228160211498054048277841)
                  ·
                    refine ⟨11421120158623540536208381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15228160211498054048277841 11421120158623540536208381)
                    ·
                      refine ⟨4282920059483827701078143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11421120158623540536208381 4282920059483827701078143)
                      ·
                        rfl

theorem cell23_8340957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_8340957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340957 prefixEnd_8340957 := by exact prefixLift 8340957
  have htrace : WordTrace (prefixWord ++ tailWord_8340957) baseStart_8340957 baseEnd_8340957 := by
    simpa [prefixWord, tailWord_8340957, baseEnd_8340957] using wordTrace_append hprefix tailTrace_8340957
  have hstable : (prefixWord ++ tailWord_8340957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340957).length < 2 ^ (prefixWord ++ tailWord_8340957).sum := by decide
  have hdescent : baseEnd_8340957 < baseStart_8340957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340977 : List Nat := [1, 2, 2, 2, 3, 2, 4, 1, 6]
def baseStart_8340977 : Nat := 118140960795 + 8340977 * 2 ^ 59
def prefixEnd_8340977 : Nat := 4983230072969 + 3 ^ 40 * 8340977 * 2
def baseEnd_8340977 : Nat := 475881147677435291425339

theorem tailTrace_8340977 : CollatzResearch.WordTrace tailWord_8340977 prefixEnd_8340977 475881147677435291425339 := by
  unfold tailWord_8340977
  simp only [CollatzResearch.WordTrace]
  refine ⟨304220423903072329304445185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202813615935381552869630123 304220423903072329304445185)
  ·
    refine ⟨228165317927304246978333889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304220423903072329304445185 228165317927304246978333889)
    ·
      refine ⟨171123988445478185233750417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228165317927304246978333889 171123988445478185233750417)
      ·
        refine ⟨128342991334108638925312813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171123988445478185233750417 128342991334108638925312813)
        ·
          refine ⟨48128621750290739596992305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128342991334108638925312813 48128621750290739596992305)
          ·
            refine ⟨36096466312718054697744229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48128621750290739596992305 36096466312718054697744229)
            ·
              refine ⟨6768087433634635255827043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36096466312718054697744229 6768087433634635255827043)
              ·
                refine ⟨10152131150451952883740565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768087433634635255827043 10152131150451952883740565)
                ·
                  refine ⟨475881147677435291425339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10152131150451952883740565 475881147677435291425339)
                  ·
                    rfl

theorem cell23_8340977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 6].length) (baseStart_8340977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340977 prefixEnd_8340977 := by exact prefixLift 8340977
  have htrace : WordTrace (prefixWord ++ tailWord_8340977) baseStart_8340977 baseEnd_8340977 := by
    simpa [prefixWord, tailWord_8340977, baseEnd_8340977] using wordTrace_append hprefix tailTrace_8340977
  have hstable : (prefixWord ++ tailWord_8340977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340977).length < 2 ^ (prefixWord ++ tailWord_8340977).sum := by decide
  have hdescent : baseEnd_8340977 < baseStart_8340977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8340983 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_8340983 : Nat := 118140960795 + 8340983 * 2 ^ 59
def prefixEnd_8340983 : Nat := 4983230072969 + 3 ^ 40 * 8340983 * 2
def baseEnd_8340983 : Nat := 4282933409980844599353023

theorem tailTrace_8340983 : CollatzResearch.WordTrace tailWord_8340983 prefixEnd_8340983 4282933409980844599353023 := by
  unfold tailWord_8340983
  simp only [CollatzResearch.WordTrace]
  refine ⟨304220642741050592329163603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202813761827367061552775735 304220642741050592329163603)
  ·
    refine ⟨456330964111575888493745405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304220642741050592329163603 456330964111575888493745405)
    ·
      refine ⟨171124111541840958185154527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456330964111575888493745405 171124111541840958185154527)
      ·
        refine ⟨256686167312761437277731791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171124111541840958185154527 256686167312761437277731791)
        ·
          refine ⟨385029250969142155916597687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256686167312761437277731791 385029250969142155916597687)
          ·
            refine ⟨577543876453713233874896531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385029250969142155916597687 577543876453713233874896531)
            ·
              refine ⟨866315814680569850812344797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577543876453713233874896531 866315814680569850812344797)
              ·
                refine ⟨324868430505213694054629299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 866315814680569850812344797 324868430505213694054629299)
                ·
                  refine ⟨487302645757820541081943949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324868430505213694054629299 487302645757820541081943949)
                  ·
                    refine ⟨182738492159182702905728981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 487302645757820541081943949 182738492159182702905728981)
                    ·
                      refine ⟨4282933409980844599353023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182738492159182702905728981 4282933409980844599353023)
                      ·
                        rfl

theorem cell23_8340983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_8340983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8340983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8340983 prefixEnd_8340983 := by exact prefixLift 8340983
  have htrace : WordTrace (prefixWord ++ tailWord_8340983) baseStart_8340983 baseEnd_8340983 := by
    simpa [prefixWord, tailWord_8340983, baseEnd_8340983] using wordTrace_append hprefix tailTrace_8340983
  have hstable : (prefixWord ++ tailWord_8340983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8340983).length < 2 ^ (prefixWord ++ tailWord_8340983).sum := by decide
  have hdescent : baseEnd_8340983 < baseStart_8340983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8340983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341020 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 3, 6]
def baseStart_8341020 : Nat := 118140960795 + 8341020 * 2 ^ 59
def prefixEnd_8341020 : Nat := 4983230072969 + 3 ^ 40 * 8341020 * 2
def baseEnd_8341020 : Nat := 1427650802921686984863451

theorem tailTrace_8341020 : CollatzResearch.WordTrace tailWord_8341020 prefixEnd_8341020 1427650802921686984863451 := by
  unfold tailWord_8341020
  simp only [CollatzResearch.WordTrace]
  refine ⟨152110996120958273824130257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202814661494611031765507009 152110996120958273824130257)
  ·
    refine ⟨114083247090718705368097693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152110996120958273824130257 114083247090718705368097693)
    ·
      refine ⟨42781217659019514513036635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114083247090718705368097693 42781217659019514513036635)
      ·
        refine ⟨64171826488529271769554953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42781217659019514513036635 64171826488529271769554953)
        ·
          refine ⟨48128869866396953827166215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64171826488529271769554953 48128869866396953827166215)
          ·
            refine ⟨72193304799595430740749323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48128869866396953827166215 72193304799595430740749323)
            ·
              refine ⟨108289957199393146111123985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72193304799595430740749323 108289957199393146111123985)
              ·
                refine ⟨81217467899544859583342989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108289957199393146111123985 81217467899544859583342989)
                ·
                  refine ⟨30456550462329322343753621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81217467899544859583342989 30456550462329322343753621)
                  ·
                    refine ⟨1427650802921686984863451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30456550462329322343753621 1427650802921686984863451)
                    ·
                      rfl

theorem cell23_8341020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_8341020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341020 prefixEnd_8341020 := by exact prefixLift 8341020
  have htrace : WordTrace (prefixWord ++ tailWord_8341020) baseStart_8341020 baseEnd_8341020 := by
    simpa [prefixWord, tailWord_8341020, baseEnd_8341020] using wordTrace_append hprefix tailTrace_8341020
  have hstable : (prefixWord ++ tailWord_8341020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341020).length < 2 ^ (prefixWord ++ tailWord_8341020).sum := by decide
  have hdescent : baseEnd_8341020 < baseStart_8341020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341021 : List Nat := [1, 4, 2, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_8341021 : Nat := 118140960795 + 8341021 * 2 ^ 59
def prefixEnd_8341021 : Nat := 4983230072969 + 3 ^ 40 * 8341021 * 2
def baseEnd_8341021 : Nat := 4282952922245715450677849

theorem tailTrace_8341021 : CollatzResearch.WordTrace tailWord_8341021 prefixEnd_8341021 4282952922245715450677849 := by
  unfold tailWord_8341021
  simp only [CollatzResearch.WordTrace]
  refine ⟨304222028714912924819046917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202814685809941949879364611 304222028714912924819046917)
  ·
    refine ⟨57041630384046173403571297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304222028714912924819046917 57041630384046173403571297)
    ·
      refine ⟨42781222788034630052678473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57041630384046173403571297 42781222788034630052678473)
      ·
        refine ⟨32085917091025972539508855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42781222788034630052678473 32085917091025972539508855)
        ·
          refine ⟨48128875636538958809263283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32085917091025972539508855 48128875636538958809263283)
          ·
            refine ⟨72193313454808438213894925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48128875636538958809263283 72193313454808438213894925)
            ·
              refine ⟨27072492545553164330210597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72193313454808438213894925 27072492545553164330210597)
              ·
                refine ⟨5076092352291218311914487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27072492545553164330210597 5076092352291218311914487)
                ·
                  refine ⟨7614138528436827467871731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076092352291218311914487 7614138528436827467871731)
                  ·
                    refine ⟨11421207792655241201807597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7614138528436827467871731 11421207792655241201807597)
                    ·
                      refine ⟨4282952922245715450677849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11421207792655241201807597 4282952922245715450677849)
                      ·
                        rfl

theorem cell23_8341021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_8341021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341021 prefixEnd_8341021 := by exact prefixLift 8341021
  have htrace : WordTrace (prefixWord ++ tailWord_8341021) baseStart_8341021 baseEnd_8341021 := by
    simpa [prefixWord, tailWord_8341021, baseEnd_8341021] using wordTrace_append hprefix tailTrace_8341021
  have hstable : (prefixWord ++ tailWord_8341021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341021).length < 2 ^ (prefixWord ++ tailWord_8341021).sum := by decide
  have hdescent : baseEnd_8341021 < baseStart_8341021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341047 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 3]
def baseStart_8341047 : Nat := 118140960795 + 8341047 * 2 ^ 59
def prefixEnd_8341047 : Nat := 4983230072969 + 3 ^ 40 * 8341047 * 2
def baseEnd_8341047 : Nat := 4282966272742732348952729

theorem tailTrace_8341047 : CollatzResearch.WordTrace tailWord_8341047 prefixEnd_8341047 4282966272742732348952729 := by
  unfold tailWord_8341047
  simp only [CollatzResearch.WordTrace]
  refine ⟨304222977012818731259493395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202815318008545820839662263 304222977012818731259493395)
  ·
    refine ⟨456334465519228096889240093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304222977012818731259493395 456334465519228096889240093)
    ·
      refine ⟨171125424569710536333465035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456334465519228096889240093 171125424569710536333465035)
      ·
        refine ⟨256688136854565804500197553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171125424569710536333465035 256688136854565804500197553)
        ·
          refine ⟨192516102640924353375148165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256688136854565804500197553 192516102640924353375148165)
          ·
            refine ⟨36096769245173316257840281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192516102640924353375148165 36096769245173316257840281)
            ·
              refine ⟨27072576933879987193380211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36096769245173316257840281 27072576933879987193380211)
              ·
                refine ⟨40608865400819980790070317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27072576933879987193380211 40608865400819980790070317)
                ·
                  refine ⟨15228324525307492796276369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40608865400819980790070317 15228324525307492796276369)
                  ·
                    refine ⟨11421243393980619597207277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15228324525307492796276369 11421243393980619597207277)
                    ·
                      refine ⟨4282966272742732348952729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11421243393980619597207277 4282966272742732348952729)
                      ·
                        rfl

theorem cell23_8341047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_8341047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341047 prefixEnd_8341047 := by exact prefixLift 8341047
  have htrace : WordTrace (prefixWord ++ tailWord_8341047) baseStart_8341047 baseEnd_8341047 := by
    simpa [prefixWord, tailWord_8341047, baseEnd_8341047] using wordTrace_append hprefix tailTrace_8341047
  have hstable : (prefixWord ++ tailWord_8341047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341047).length < 2 ^ (prefixWord ++ tailWord_8341047).sum := by decide
  have hdescent : baseEnd_8341047 < baseStart_8341047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341057 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_8341057 : Nat := 118140960795 + 8341057 * 2 ^ 59
def prefixEnd_8341057 : Nat := 4983230072969 + 3 ^ 40 * 8341057 * 2
def baseEnd_8341057 : Nat := 4282971407549277309827683

theorem tailTrace_8341057 : CollatzResearch.WordTrace tailWord_8341057 prefixEnd_8341057 4282971407549277309827683 := by
  unfold tailWord_8341057
  simp only [CollatzResearch.WordTrace]
  refine ⟨304223341742782502967357425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202815561161855001978238283 304223341742782502967357425)
  ·
    refine ⟨228167506307086877225518069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304223341742782502967357425 228167506307086877225518069)
    ·
      refine ⟨21390703716289394739892319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228167506307086877225518069 21390703716289394739892319)
      ·
        refine ⟨32086055574434092109838479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21390703716289394739892319 32086055574434092109838479)
        ·
          refine ⟨48129083361651138164757719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32086055574434092109838479 48129083361651138164757719)
          ·
            refine ⟨72193625042476707247136579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48129083361651138164757719 72193625042476707247136579)
            ·
              refine ⟨108290437563715060870704869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72193625042476707247136579 108290437563715060870704869)
              ·
                refine ⟨20304457043196573913257163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108290437563715060870704869 20304457043196573913257163)
                ·
                  refine ⟨30456685564794860869885745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20304457043196573913257163 30456685564794860869885745)
                  ·
                    refine ⟨22842514173596145652414309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30456685564794860869885745 22842514173596145652414309)
                    ·
                      refine ⟨4282971407549277309827683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22842514173596145652414309 4282971407549277309827683)
                      ·
                        rfl

theorem cell23_8341057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_8341057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341057 prefixEnd_8341057 := by exact prefixLift 8341057
  have htrace : WordTrace (prefixWord ++ tailWord_8341057) baseStart_8341057 baseEnd_8341057 := by
    simpa [prefixWord, tailWord_8341057, baseEnd_8341057] using wordTrace_append hprefix tailTrace_8341057
  have hstable : (prefixWord ++ tailWord_8341057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341057).length < 2 ^ (prefixWord ++ tailWord_8341057).sum := by decide
  have hdescent : baseEnd_8341057 < baseStart_8341057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341070 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_8341070 : Nat := 118140960795 + 8341070 * 2 ^ 59
def prefixEnd_8341070 : Nat := 4983230072969 + 3 ^ 40 * 8341070 * 2
def baseEnd_8341070 : Nat := 4282978082797785758965123

theorem tailTrace_8341070 : CollatzResearch.WordTrace tailWord_8341070 prefixEnd_8341070 4282978082797785758965123 := by
  unfold tailWord_8341070
  simp only [CollatzResearch.WordTrace]
  refine ⟨38027976986466925773447583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202815877261156937458387109 38027976986466925773447583)
  ·
    refine ⟨57041965479700388660171375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38027976986466925773447583 57041965479700388660171375)
    ·
      refine ⟨85562948219550582990257063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57041965479700388660171375 85562948219550582990257063)
      ·
        refine ⟨128344422329325874485385595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85562948219550582990257063 128344422329325874485385595)
        ·
          refine ⟨192516633493988811728078393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128344422329325874485385595 192516633493988811728078393)
          ·
            refine ⟨144387475120491608796058795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192516633493988811728078393 144387475120491608796058795)
            ·
              refine ⟨216581212680737413194088193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144387475120491608796058795 216581212680737413194088193)
              ·
                refine ⟨162435909510553059895566145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216581212680737413194088193 162435909510553059895566145)
                ·
                  refine ⟨121826932132914794921674609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162435909510553059895566145 121826932132914794921674609)
                  ·
                    refine ⟨91370199099686096191255957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121826932132914794921674609 91370199099686096191255957)
                    ·
                      refine ⟨4282978082797785758965123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91370199099686096191255957 4282978082797785758965123)
                      ·
                        rfl

theorem cell23_8341070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_8341070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341070 prefixEnd_8341070 := by exact prefixLift 8341070
  have htrace : WordTrace (prefixWord ++ tailWord_8341070) baseStart_8341070 baseEnd_8341070 := by
    simpa [prefixWord, tailWord_8341070, baseEnd_8341070] using wordTrace_append hprefix tailTrace_8341070
  have hstable : (prefixWord ++ tailWord_8341070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341070).length < 2 ^ (prefixWord ++ tailWord_8341070).sum := by decide
  have hdescent : baseEnd_8341070 < baseStart_8341070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341101 : List Nat := [1, 5, 1, 1, 5, 1, 2, 7]
def baseStart_8341101 : Nat := 118140960795 + 8341101 * 2 ^ 59
def prefixEnd_8341101 : Nat := 4983230072969 + 3 ^ 40 * 8341101 * 2
def baseEnd_8341101 : Nat := 158629407433262042136203

theorem tailTrace_8341101 : CollatzResearch.WordTrace tailWord_8341101 prefixEnd_8341101 158629407433262042136203 := by
  unfold tailWord_8341101
  simp only [CollatzResearch.WordTrace]
  refine ⟨304224946554623098481959157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202816631036415398987972771 304224946554623098481959157)
  ·
    refine ⟨28521088739495915482683671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304224946554623098481959157 28521088739495915482683671)
    ·
      refine ⟨42781633109243873224025507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28521088739495915482683671 42781633109243873224025507)
      ·
        refine ⟨64172449663865809836038261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42781633109243873224025507 64172449663865809836038261)
        ·
          refine ⟨6016167155987419672128587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64172449663865809836038261 6016167155987419672128587)
          ·
            refine ⟨9024250733981129508192881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6016167155987419672128587 9024250733981129508192881)
            ·
              refine ⟨6768188050485847131144661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9024250733981129508192881 6768188050485847131144661)
              ·
                refine ⟨158629407433262042136203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6768188050485847131144661 158629407433262042136203)
                ·
                  rfl

theorem cell23_8341101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 7].length) (baseStart_8341101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341101 prefixEnd_8341101 := by exact prefixLift 8341101
  have htrace : WordTrace (prefixWord ++ tailWord_8341101) baseStart_8341101 baseEnd_8341101 := by
    simpa [prefixWord, tailWord_8341101, baseEnd_8341101] using wordTrace_append hprefix tailTrace_8341101
  have hstable : (prefixWord ++ tailWord_8341101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341101).length < 2 ^ (prefixWord ++ tailWord_8341101).sum := by decide
  have hdescent : baseEnd_8341101 < baseStart_8341101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341121 : List Nat := [1, 2, 4, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_8341121 : Nat := 118140960795 + 8341121 * 2 ^ 59
def prefixEnd_8341121 : Nat := 4983230072969 + 3 ^ 40 * 8341121 * 2
def baseEnd_8341121 : Nat := 4283004270311165059427389

theorem tailTrace_8341121 : CollatzResearch.WordTrace tailWord_8341121 prefixEnd_8341121 4283004270311165059427389 := by
  unfold tailWord_8341121
  simp only [CollatzResearch.WordTrace]
  refine ⟨304225676014550641897687217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202817117343033761265124811 304225676014550641897687217)
  ·
    refine ⟨228169257010912981423265413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304225676014550641897687217 228169257010912981423265413)
    ·
      refine ⟨42781735689546184016862265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228169257010912981423265413 42781735689546184016862265)
      ·
        refine ⟨32086301767159638012646699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42781735689546184016862265 32086301767159638012646699)
        ·
          refine ⟨48129452650739457018970049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32086301767159638012646699 48129452650739457018970049)
          ·
            refine ⟨36097089488054592764227537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48129452650739457018970049 36097089488054592764227537)
            ·
              refine ⟨27072817116040944573170653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36097089488054592764227537 27072817116040944573170653)
              ·
                refine ⟨10152306418515354214938995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27072817116040944573170653 10152306418515354214938995)
                ·
                  refine ⟨15228459627773031322408493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10152306418515354214938995 15228459627773031322408493)
                  ·
                    refine ⟨5710672360414886745903185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15228459627773031322408493 5710672360414886745903185)
                    ·
                      refine ⟨4283004270311165059427389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5710672360414886745903185 4283004270311165059427389)
                      ·
                        rfl

theorem cell23_8341121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_8341121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341121 prefixEnd_8341121 := by exact prefixLift 8341121
  have htrace : WordTrace (prefixWord ++ tailWord_8341121) baseStart_8341121 baseEnd_8341121 := by
    simpa [prefixWord, tailWord_8341121, baseEnd_8341121] using wordTrace_append hprefix tailTrace_8341121
  have hstable : (prefixWord ++ tailWord_8341121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341121).length < 2 ^ (prefixWord ++ tailWord_8341121).sum := by decide
  have hdescent : baseEnd_8341121 < baseStart_8341121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341207 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_8341207 : Nat := 118140960795 + 8341207 * 2 ^ 59
def prefixEnd_8341207 : Nat := 4983230072969 + 3 ^ 40 * 8341207 * 2
def baseEnd_8341207 : Nat := 4283048429647451722951993

theorem tailTrace_8341207 : CollatzResearch.WordTrace tailWord_8341207 prefixEnd_8341207 4283048429647451722951993 := by
  unfold tailWord_8341207
  simp only [CollatzResearch.WordTrace]
  refine ⟨304228812692239078585317875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202819208461492719056878583 304228812692239078585317875)
  ·
    refine ⟨456343219038358617877976813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304228812692239078585317875 456343219038358617877976813)
    ·
      refine ⟨171128707139384481704241305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456343219038358617877976813 171128707139384481704241305)
      ·
        refine ⟨128346530354538361278180979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171128707139384481704241305 128346530354538361278180979)
        ·
          refine ⟨192519795531807541917271469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128346530354538361278180979 192519795531807541917271469)
          ·
            refine ⟨72194923324427828218976801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192519795531807541917271469 72194923324427828218976801)
            ·
              refine ⟨54146192493320871164232601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72194923324427828218976801 54146192493320871164232601)
              ·
                refine ⟨40609644369990653373174451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54146192493320871164232601 40609644369990653373174451)
                ·
                  refine ⟨60914466554985980059761677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40609644369990653373174451 60914466554985980059761677)
                  ·
                    refine ⟨22842924958119742522410629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60914466554985980059761677 22842924958119742522410629)
                    ·
                      refine ⟨4283048429647451722951993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22842924958119742522410629 4283048429647451722951993)
                      ·
                        rfl

theorem cell23_8341207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_8341207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341207 prefixEnd_8341207 := by exact prefixLift 8341207
  have htrace : WordTrace (prefixWord ++ tailWord_8341207) baseStart_8341207 baseEnd_8341207 := by
    simpa [prefixWord, tailWord_8341207, baseEnd_8341207] using wordTrace_append hprefix tailTrace_8341207
  have hstable : (prefixWord ++ tailWord_8341207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341207).length < 2 ^ (prefixWord ++ tailWord_8341207).sum := by decide
  have hdescent : baseEnd_8341207 < baseStart_8341207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341224 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_8341224 : Nat := 118140960795 + 8341224 * 2 ^ 59
def prefixEnd_8341224 : Nat := 4983230072969 + 3 ^ 40 * 8341224 * 2
def baseEnd_8341224 : Nat := 4283057158818578156439415

theorem tailTrace_8341224 : CollatzResearch.WordTrace tailWord_8341224 prefixEnd_8341224 4283057158818578156439415 := by
  unfold tailWord_8341224
  simp only [CollatzResearch.WordTrace]
  refine ⟨152114716366588745244343363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202819621822118326992457817 152114716366588745244343363)
  ·
    refine ⟨228172074549883117866515045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152114716366588745244343363 228172074549883117866515045)
    ·
      refine ⟨42782263978103084599971571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228172074549883117866515045 42782263978103084599971571)
      ·
        refine ⟨64173395967154626899957357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42782263978103084599971571 64173395967154626899957357)
        ·
          refine ⟨24065023487682985087484009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64173395967154626899957357 24065023487682985087484009)
          ·
            refine ⟨18048767615762238815613007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24065023487682985087484009 18048767615762238815613007)
            ·
              refine ⟨27073151423643358223419511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18048767615762238815613007 27073151423643358223419511)
              ·
                refine ⟨40609727135465037335129267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27073151423643358223419511 40609727135465037335129267)
                ·
                  refine ⟨60914590703197556002693901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40609727135465037335129267 60914590703197556002693901)
                  ·
                    refine ⟨22842971513699083501010213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60914590703197556002693901 22842971513699083501010213)
                    ·
                      refine ⟨4283057158818578156439415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22842971513699083501010213 4283057158818578156439415)
                      ·
                        rfl

theorem cell23_8341224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_8341224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341224 prefixEnd_8341224 := by exact prefixLift 8341224
  have htrace : WordTrace (prefixWord ++ tailWord_8341224) baseStart_8341224 baseEnd_8341224 := by
    simpa [prefixWord, tailWord_8341224, baseEnd_8341224] using wordTrace_append hprefix tailTrace_8341224
  have hstable : (prefixWord ++ tailWord_8341224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341224).length < 2 ^ (prefixWord ++ tailWord_8341224).sum := by decide
  have hdescent : baseEnd_8341224 < baseStart_8341224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341234 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_8341234 : Nat := 118140960795 + 8341234 * 2 ^ 59
def prefixEnd_8341234 : Nat := 4983230072969 + 3 ^ 40 * 8341234 * 2
def baseEnd_8341234 : Nat := 1427687431208374372438123

theorem tailTrace_8341234 : CollatzResearch.WordTrace tailWord_8341234 prefixEnd_8341234 1427687431208374372438123 := by
  unfold tailWord_8341234
  simp only [CollatzResearch.WordTrace]
  refine ⟨76057449365785315549137689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202819864975427508131033837 76057449365785315549137689)
  ·
    refine ⟨57043087024338986661853267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76057449365785315549137689 57043087024338986661853267)
    ·
      refine ⟨85564630536508479992779901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57043087024338986661853267 85564630536508479992779901)
      ·
        refine ⟨32086736451190679997292463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85564630536508479992779901 32086736451190679997292463)
        ·
          refine ⟨48130104676786019995938695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32086736451190679997292463 48130104676786019995938695)
          ·
            refine ⟨72195157015179029993908043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48130104676786019995938695 72195157015179029993908043)
            ·
              refine ⟨108292735522768544990862065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72195157015179029993908043 108292735522768544990862065)
              ·
                refine ⟨81219551642076408743146549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108292735522768544990862065 81219551642076408743146549)
                ·
                  refine ⟨7614332966444663319669989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81219551642076408743146549 7614332966444663319669989)
                  ·
                    refine ⟨1427687431208374372438123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7614332966444663319669989 1427687431208374372438123)
                    ·
                      rfl

theorem cell23_8341234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_8341234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341234 prefixEnd_8341234 := by exact prefixLift 8341234
  have htrace : WordTrace (prefixWord ++ tailWord_8341234) baseStart_8341234 baseEnd_8341234 := by
    simpa [prefixWord, tailWord_8341234, baseEnd_8341234] using wordTrace_append hprefix tailTrace_8341234
  have hstable : (prefixWord ++ tailWord_8341234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341234).length < 2 ^ (prefixWord ++ tailWord_8341234).sum := by decide
  have hdescent : baseEnd_8341234 < baseStart_8341234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341244 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_8341244 : Nat := 118140960795 + 8341244 * 2 ^ 59
def prefixEnd_8341244 : Nat := 4983230072969 + 3 ^ 40 * 8341244 * 2
def baseEnd_8341244 : Nat := 4283067428431668078189323

theorem tailTrace_8341244 : CollatzResearch.WordTrace tailWord_8341244 prefixEnd_8341244 4283067428431668078189323 := by
  unfold tailWord_8341244
  simp only [CollatzResearch.WordTrace]
  refine ⟨152115081096552516952207393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202820108128736689269609857 152115081096552516952207393)
  ·
    refine ⟨114086310822414387714155545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152115081096552516952207393 114086310822414387714155545)
    ·
      refine ⟨85564733116810790785616659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114086310822414387714155545 85564733116810790785616659)
      ·
        refine ⟨128347099675216186178424989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85564733116810790785616659 128347099675216186178424989)
        ·
          refine ⟨48130162378206069816909371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128347099675216186178424989 48130162378206069816909371)
          ·
            refine ⟨72195243567309104725364057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48130162378206069816909371 72195243567309104725364057)
            ·
              refine ⟨54146432675481828544023043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72195243567309104725364057 54146432675481828544023043)
              ·
                refine ⟨81219649013222742816034565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54146432675481828544023043 81219649013222742816034565)
                ·
                  refine ⟨15228684189979264278006481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81219649013222742816034565 15228684189979264278006481)
                  ·
                    refine ⟨11421513142484448208504861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15228684189979264278006481 11421513142484448208504861)
                    ·
                      refine ⟨4283067428431668078189323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11421513142484448208504861 4283067428431668078189323)
                      ·
                        rfl

theorem cell23_8341244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_8341244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341244 prefixEnd_8341244 := by exact prefixLift 8341244
  have htrace : WordTrace (prefixWord ++ tailWord_8341244) baseStart_8341244 baseEnd_8341244 := by
    simpa [prefixWord, tailWord_8341244, baseEnd_8341244] using wordTrace_append hprefix tailTrace_8341244
  have hstable : (prefixWord ++ tailWord_8341244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341244).length < 2 ^ (prefixWord ++ tailWord_8341244).sum := by decide
  have hdescent : baseEnd_8341244 < baseStart_8341244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341251 : List Nat := [1, 1, 1, 3, 2, 2, 4, 4, 1, 4]
def baseStart_8341251 : Nat := 118140960795 + 8341251 * 2 ^ 59
def prefixEnd_8341251 : Nat := 4983230072969 + 3 ^ 40 * 8341251 * 2
def baseEnd_8341251 : Nat := 1427690340932083183600597

theorem tailTrace_8341251 : CollatzResearch.WordTrace tailWord_8341251 prefixEnd_8341251 1427690340932083183600597 := by
  unfold tailWord_8341251
  simp only [CollatzResearch.WordTrace]
  refine ⟨304230417504079674099919607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202820278336053116066613071 304230417504079674099919607)
  ·
    refine ⟨456345626256119511149879411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304230417504079674099919607 456345626256119511149879411)
    ·
      refine ⟨684518439384179266724819117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456345626256119511149879411 684518439384179266724819117)
      ·
        refine ⟨256694414769067225021807169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 684518439384179266724819117 256694414769067225021807169)
        ·
          refine ⟨192520811076800418766355377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256694414769067225021807169 192520811076800418766355377)
          ·
            refine ⟨144390608307600314074766533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192520811076800418766355377 144390608307600314074766533)
            ·
              refine ⟨27073239057675058889018725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144390608307600314074766533 27073239057675058889018725)
              ·
                refine ⟨5076232323314073541691011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27073239057675058889018725 5076232323314073541691011)
                ·
                  refine ⟨7614348484971110312536517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076232323314073541691011 7614348484971110312536517)
                  ·
                    refine ⟨1427690340932083183600597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7614348484971110312536517 1427690340932083183600597)
                    ·
                      rfl

theorem cell23_8341251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 1, 4].length) (baseStart_8341251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341251 prefixEnd_8341251 := by exact prefixLift 8341251
  have htrace : WordTrace (prefixWord ++ tailWord_8341251) baseStart_8341251 baseEnd_8341251 := by
    simpa [prefixWord, tailWord_8341251, baseEnd_8341251] using wordTrace_append hprefix tailTrace_8341251
  have hstable : (prefixWord ++ tailWord_8341251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341251).length < 2 ^ (prefixWord ++ tailWord_8341251).sum := by decide
  have hdescent : baseEnd_8341251 < baseStart_8341251 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341302 : List Nat := [5, 1, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_8341302 : Nat := 118140960795 + 8341302 * 2 ^ 59
def prefixEnd_8341302 : Nat := 4983230072969 + 3 ^ 40 * 8341302 * 2
def baseEnd_8341302 : Nat := 1427699070103209617088019

theorem tailTrace_8341302 : CollatzResearch.WordTrace tailWord_8341302 prefixEnd_8341302 1427699070103209617088019 := by
  unfold tailWord_8341302
  simp only [CollatzResearch.WordTrace]
  refine ⟨19014517351680931863126635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202821518417929939873350773 19014517351680931863126635)
  ·
    refine ⟨28521776027521397794689953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19014517351680931863126635 28521776027521397794689953)
    ·
      refine ⟨21391332020641048346017465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28521776027521397794689953 21391332020641048346017465)
      ·
        refine ⟨16043499015480786259513099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21391332020641048346017465 16043499015480786259513099)
        ·
          refine ⟨24065248523221179389269649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16043499015480786259513099 24065248523221179389269649)
          ·
            refine ⟨18048936392415884541952237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24065248523221179389269649 18048936392415884541952237)
            ·
              refine ⟨6768351147155956703232089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18048936392415884541952237 6768351147155956703232089)
              ·
                refine ⟨5076263360366967527424067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6768351147155956703232089 5076263360366967527424067)
                ·
                  refine ⟨7614395040550451291136101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076263360366967527424067 7614395040550451291136101)
                  ·
                    refine ⟨1427699070103209617088019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7614395040550451291136101 1427699070103209617088019)
                    ·
                      rfl

theorem cell23_8341302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_8341302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341302 prefixEnd_8341302 := by exact prefixLift 8341302
  have htrace : WordTrace (prefixWord ++ tailWord_8341302) baseStart_8341302 baseEnd_8341302 := by
    simpa [prefixWord, tailWord_8341302, baseEnd_8341302] using wordTrace_append hprefix tailTrace_8341302
  have hstable : (prefixWord ++ tailWord_8341302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341302).length < 2 ^ (prefixWord ++ tailWord_8341302).sum := by decide
  have hdescent : baseEnd_8341302 < baseStart_8341302 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341308 : List Nat := [2, 2, 2, 2, 1, 1, 2, 6, 1, 1, 3]
def baseStart_8341308 : Nat := 118140960795 + 8341308 * 2 ^ 59
def prefixEnd_8341308 : Nat := 4983230072969 + 3 ^ 40 * 8341308 * 2
def baseEnd_8341308 : Nat := 4283100291193555827789029

theorem tailTrace_8341308 : CollatzResearch.WordTrace tailWord_8341308 prefixEnd_8341308 4283100291193555827789029 := by
  unfold tailWord_8341308
  simp only [CollatzResearch.WordTrace]
  refine ⟨152116248232436586417372289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202821664309915448556496385 152116248232436586417372289)
  ·
    refine ⟨114087186174327439813029217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152116248232436586417372289 114087186174327439813029217)
    ·
      refine ⟨85565389630745579859771913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114087186174327439813029217 85565389630745579859771913)
      ·
        refine ⟨64174042223059184894828935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85565389630745579859771913 64174042223059184894828935)
        ·
          refine ⟨96261063334588777342243403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64174042223059184894828935 96261063334588777342243403)
          ·
            refine ⟨144391595001883166013365105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96261063334588777342243403 144391595001883166013365105)
            ·
              refine ⟨108293696251412374510023829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144391595001883166013365105 108293696251412374510023829)
              ·
                refine ⟨5076267011784955055157367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108293696251412374510023829 5076267011784955055157367)
                ·
                  refine ⟨7614400517677432582736051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076267011784955055157367 7614400517677432582736051)
                  ·
                    refine ⟨11421600776516148874104077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7614400517677432582736051 11421600776516148874104077)
                    ·
                      refine ⟨4283100291193555827789029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11421600776516148874104077 4283100291193555827789029)
                      ·
                        rfl

theorem cell23_8341308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_8341308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341308 prefixEnd_8341308 := by exact prefixLift 8341308
  have htrace : WordTrace (prefixWord ++ tailWord_8341308) baseStart_8341308 baseEnd_8341308 := by
    simpa [prefixWord, tailWord_8341308, baseEnd_8341308] using wordTrace_append hprefix tailTrace_8341308
  have hstable : (prefixWord ++ tailWord_8341308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341308).length < 2 ^ (prefixWord ++ tailWord_8341308).sum := by decide
  have hdescent : baseEnd_8341308 < baseStart_8341308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341337 : List Nat := [1, 2, 1, 2, 2, 3, 1, 11]
def baseStart_8341337 : Nat := 118140960795 + 8341337 * 2 ^ 59
def prefixEnd_8341337 : Nat := 4983230072969 + 3 ^ 40 * 8341337 * 2
def baseEnd_8341337 : Nat := 158633895634538378308385

theorem tailTrace_8341337 : CollatzResearch.WordTrace tailWord_8341337 prefixEnd_8341337 158633895634538378308385 := by
  unfold tailWord_8341337
  simp only [CollatzResearch.WordTrace]
  refine ⟨304233554181768110787550265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202822369454512073858366843 304233554181768110787550265)
  ·
    refine ⟨228175165636326083090662699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304233554181768110787550265 228175165636326083090662699)
    ·
      refine ⟨342262748454489124635994049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228175165636326083090662699 342262748454489124635994049)
      ·
        refine ⟨256697061340866843476995537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342262748454489124635994049 256697061340866843476995537)
        ·
          refine ⟨192522796005650132607746653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256697061340866843476995537 192522796005650132607746653)
          ·
            refine ⟨72196048502118799727904995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192522796005650132607746653 72196048502118799727904995)
            ·
              refine ⟨108294072753178199591857493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72196048502118799727904995 108294072753178199591857493)
              ·
                refine ⟨158633895634538378308385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 108294072753178199591857493 158633895634538378308385)
                ·
                  rfl

theorem cell23_8341337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 11].length) (baseStart_8341337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341337 prefixEnd_8341337 := by exact prefixLift 8341337
  have htrace : WordTrace (prefixWord ++ tailWord_8341337) baseStart_8341337 baseEnd_8341337 := by
    simpa [prefixWord, tailWord_8341337, baseEnd_8341337] using wordTrace_append hprefix tailTrace_8341337
  have hstable : (prefixWord ++ tailWord_8341337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341337).length < 2 ^ (prefixWord ++ tailWord_8341337).sum := by decide
  have hdescent : baseEnd_8341337 < baseStart_8341337 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341344 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 4]
def baseStart_8341344 : Nat := 118140960795 + 8341344 * 2 ^ 59
def prefixEnd_8341344 : Nat := 4983230072969 + 3 ^ 40 * 8341344 * 2
def baseEnd_8341344 : Nat := 4283118776497117686938863

theorem tailTrace_8341344 : CollatzResearch.WordTrace tailWord_8341344 prefixEnd_8341344 4283118776497117686938863 := by
  unfold tailWord_8341344
  simp only [CollatzResearch.WordTrace]
  refine ⟨152116904746371375491527543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202822539661828500655370057 152116904746371375491527543)
  ·
    refine ⟨228175357119557063237291315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152116904746371375491527543 228175357119557063237291315)
    ·
      refine ⟨342263035679335594855936973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228175357119557063237291315 342263035679335594855936973)
      ·
        refine ⟨128348638379750848070976365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342263035679335594855936973 128348638379750848070976365)
        ·
          refine ⟨48130739392406568026616137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128348638379750848070976365 48130739392406568026616137)
          ·
            refine ⟨36098054544304926019962103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48130739392406568026616137 36098054544304926019962103)
            ·
              refine ⟨54147081816457389029943155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36098054544304926019962103 54147081816457389029943155)
              ·
                refine ⟨81220622724686083544914733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54147081816457389029943155 81220622724686083544914733)
                ·
                  refine ⟨30457733521757281329343025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81220622724686083544914733 30457733521757281329343025)
                  ·
                    refine ⟨22843300141317960997007269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30457733521757281329343025 22843300141317960997007269)
                    ·
                      refine ⟨4283118776497117686938863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22843300141317960997007269 4283118776497117686938863)
                      ·
                        rfl

theorem cell23_8341344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_8341344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341344 prefixEnd_8341344 := by exact prefixLift 8341344
  have htrace : WordTrace (prefixWord ++ tailWord_8341344) baseStart_8341344 baseEnd_8341344 := by
    simpa [prefixWord, tailWord_8341344, baseEnd_8341344] using wordTrace_append hprefix tailTrace_8341344
  have hstable : (prefixWord ++ tailWord_8341344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341344).length < 2 ^ (prefixWord ++ tailWord_8341344).sum := by decide
  have hdescent : baseEnd_8341344 < baseStart_8341344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341354 : List Nat := [3, 1, 3, 4, 12]
def baseStart_8341354 : Nat := 118140960795 + 8341354 * 2 ^ 59
def prefixEnd_8341354 : Nat := 4983230072969 + 3 ^ 40 * 8341354 * 2
def baseEnd_8341354 : Nat := 5875341442117507061473

theorem tailTrace_8341354 : CollatzResearch.WordTrace tailWord_8341354 prefixEnd_8341354 5875341442117507061473 := by
  unfold tailWord_8341354
  simp only [CollatzResearch.WordTrace]
  refine ⟨76058543555676630672729779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202822782815137681793946077 76058543555676630672729779)
  ·
    refine ⟨114087815333514946009094669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76058543555676630672729779 114087815333514946009094669)
    ·
      refine ⟨42782930750068104753410501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114087815333514946009094669 42782930750068104753410501)
      ·
        refine ⟨8021799515637769641264469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42782930750068104753410501 8021799515637769641264469)
        ·
          refine ⟨5875341442117507061473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 8021799515637769641264469 5875341442117507061473)
          ·
            rfl

theorem cell23_8341354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 12].length) (baseStart_8341354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341354 prefixEnd_8341354 := by exact prefixLift 8341354
  have htrace : WordTrace (prefixWord ++ tailWord_8341354) baseStart_8341354 baseEnd_8341354 := by
    simpa [prefixWord, tailWord_8341354, baseEnd_8341354] using wordTrace_append hprefix tailTrace_8341354
  have hstable : (prefixWord ++ tailWord_8341354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341354).length < 2 ^ (prefixWord ++ tailWord_8341354).sum := by decide
  have hdescent : baseEnd_8341354 < baseStart_8341354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341358 : List Nat := [4, 1, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_8341358 : Nat := 118140960795 + 8341358 * 2 ^ 59
def prefixEnd_8341358 : Nat := 4983230072969 + 3 ^ 40 * 8341358 * 2
def baseEnd_8341358 : Nat := 1427708655075426877387933

theorem tailTrace_8341358 : CollatzResearch.WordTrace tailWord_8341358 prefixEnd_8341358 1427708655075426877387933 := by
  unfold tailWord_8341358
  simp only [CollatzResearch.WordTrace]
  refine ⟨38029290014336503921758091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202822880076461354249376485 38029290014336503921758091)
  ·
    refine ⟨57043935021504755882637137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38029290014336503921758091 57043935021504755882637137)
    ·
      refine ⟨42782951266128566911977853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57043935021504755882637137 42782951266128566911977853)
      ·
        refine ⟨16043606724798212591991695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42782951266128566911977853 16043606724798212591991695)
        ·
          refine ⟨24065410087197318887987543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16043606724798212591991695 24065410087197318887987543)
          ·
            refine ⟨36098115130795978331981315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24065410087197318887987543 36098115130795978331981315)
            ·
              refine ⟨54147172696193967497971973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36098115130795978331981315 54147172696193967497971973)
              ·
                refine ⟨10152594880536368905869745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54147172696193967497971973 10152594880536368905869745)
                ·
                  refine ⟨7614446160402276679402309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10152594880536368905869745 7614446160402276679402309)
                  ·
                    refine ⟨1427708655075426877387933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7614446160402276679402309 1427708655075426877387933)
                    ·
                      rfl

theorem cell23_8341358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_8341358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341358 prefixEnd_8341358 := by exact prefixLift 8341358
  have htrace : WordTrace (prefixWord ++ tailWord_8341358) baseStart_8341358 baseEnd_8341358 := by
    simpa [prefixWord, tailWord_8341358, baseEnd_8341358] using wordTrace_append hprefix tailTrace_8341358
  have hstable : (prefixWord ++ tailWord_8341358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341358).length < 2 ^ (prefixWord ++ tailWord_8341358).sum := by decide
  have hdescent : baseEnd_8341358 < baseStart_8341358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341381 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 1, 3, 3]
def baseStart_8341381 : Nat := 118140960795 + 8341381 * 2 ^ 59
def prefixEnd_8341381 : Nat := 4983230072969 + 3 ^ 40 * 8341381 * 2
def baseEnd_8341381 : Nat := 4283137775281334042176193

theorem tailTrace_8341381 : CollatzResearch.WordTrace tailWord_8341381 prefixEnd_8341381 4283137775281334042176193 := by
  unfold tailWord_8341381
  simp only [CollatzResearch.WordTrace]
  refine ⟨304235158993608706302151997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202823439329072470868101331 304235158993608706302151997)
  ·
    refine ⟨114088184622603264863306999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304235158993608706302151997 114088184622603264863306999)
    ·
      refine ⟨171132276933904897294960499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114088184622603264863306999 171132276933904897294960499)
      ·
        refine ⟨256698415400857345942440749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171132276933904897294960499 256698415400857345942440749)
        ·
          refine ⟨96261905775321504728415281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256698415400857345942440749 96261905775321504728415281)
          ·
            refine ⟨72196429331491128546311461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96261905775321504728415281 72196429331491128546311461)
            ·
              refine ⟨13536830499654586602433399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72196429331491128546311461 13536830499654586602433399)
              ·
                refine ⟨20305245749481879903650099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13536830499654586602433399 20305245749481879903650099)
                ·
                  refine ⟨30457868624222819855475149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20305245749481879903650099 30457868624222819855475149)
                  ·
                    refine ⟨11421700734083557445803181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30457868624222819855475149 11421700734083557445803181)
                    ·
                      refine ⟨4283137775281334042176193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11421700734083557445803181 4283137775281334042176193)
                      ·
                        rfl

theorem cell23_8341381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_8341381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341381 prefixEnd_8341381 := by exact prefixLift 8341381
  have htrace : WordTrace (prefixWord ++ tailWord_8341381) baseStart_8341381 baseEnd_8341381 := by
    simpa [prefixWord, tailWord_8341381, baseEnd_8341381] using wordTrace_append hprefix tailTrace_8341381
  have hstable : (prefixWord ++ tailWord_8341381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341381).length < 2 ^ (prefixWord ++ tailWord_8341381).sum := by decide
  have hdescent : baseEnd_8341381 < baseStart_8341381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341415 : List Nat := [1, 1, 6, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_8341415 : Nat := 118140960795 + 8341415 * 2 ^ 59
def prefixEnd_8341415 : Nat := 4983230072969 + 3 ^ 40 * 8341415 * 2
def baseEnd_8341415 : Nat := 4283155233623586909151037

theorem tailTrace_8341415 : CollatzResearch.WordTrace tailWord_8341415 prefixEnd_8341415 4283155233623586909151037 := by
  unfold tailWord_8341415
  simp only [CollatzResearch.WordTrace]
  refine ⟨304236399075485530108889699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202824266050323686739259799 304236399075485530108889699)
  ·
    refine ⟨456354598613228295163334549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304236399075485530108889699 456354598613228295163334549)
    ·
      refine ⟨21391621809995076335781307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 456354598613228295163334549 21391621809995076335781307)
      ·
        refine ⟨32087432714992614503671961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21391621809995076335781307 32087432714992614503671961)
        ·
          refine ⟨24065574536244460877753971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32087432714992614503671961 24065574536244460877753971)
          ·
            refine ⟨36098361804366691316630957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24065574536244460877753971 36098361804366691316630957)
            ·
              refine ⟨13536885676637509243736609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36098361804366691316630957 13536885676637509243736609)
              ·
                refine ⟨10152664257478131932802457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13536885676637509243736609 10152664257478131932802457)
                ·
                  refine ⟨7614498193108598949601843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10152664257478131932802457 7614498193108598949601843)
                  ·
                    refine ⟨11421747289662898424402765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7614498193108598949601843 11421747289662898424402765)
                    ·
                      refine ⟨4283155233623586909151037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11421747289662898424402765 4283155233623586909151037)
                      ·
                        rfl

theorem cell23_8341415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_8341415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341415 prefixEnd_8341415 := by exact prefixLift 8341415
  have htrace : WordTrace (prefixWord ++ tailWord_8341415) baseStart_8341415 baseEnd_8341415 := by
    simpa [prefixWord, tailWord_8341415, baseEnd_8341415] using wordTrace_append hprefix tailTrace_8341415
  have hstable : (prefixWord ++ tailWord_8341415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341415).length < 2 ^ (prefixWord ++ tailWord_8341415).sum := by decide
  have hdescent : baseEnd_8341415 < baseStart_8341415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341434 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_8341434 : Nat := 118140960795 + 8341434 * 2 ^ 59
def prefixEnd_8341434 : Nat := 4983230072969 + 3 ^ 40 * 8341434 * 2
def baseEnd_8341434 : Nat := 4283164989756022334813449

theorem tailTrace_8341434 : CollatzResearch.WordTrace tailWord_8341434 prefixEnd_8341434 4283164989756022334813449 := by
  unfold tailWord_8341434
  simp only [CollatzResearch.WordTrace]
  refine ⟨76059273015604174088457839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202824728041611130902554237 76059273015604174088457839)
  ·
    refine ⟨114088909523406261132686759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76059273015604174088457839 114088909523406261132686759)
    ·
      refine ⟨171133364285109391699030139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114088909523406261132686759 171133364285109391699030139)
      ·
        refine ⟨256700046427664087548545209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171133364285109391699030139 256700046427664087548545209)
        ·
          refine ⟨192525034820748065661408907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256700046427664087548545209 192525034820748065661408907)
          ·
            refine ⟨288787552231122098492113361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192525034820748065661408907 288787552231122098492113361)
            ·
              refine ⟨216590664173341573869085021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288787552231122098492113361 216590664173341573869085021)
              ·
                refine ⟨81221499065003090200906883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216590664173341573869085021 81221499065003090200906883)
                ·
                  refine ⟨121832248597504635301360325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81221499065003090200906883 121832248597504635301360325)
                  ·
                    refine ⟨22843546612032119119005061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121832248597504635301360325 22843546612032119119005061)
                    ·
                      refine ⟨4283164989756022334813449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22843546612032119119005061 4283164989756022334813449)
                      ·
                        rfl

theorem cell23_8341434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_8341434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341434 prefixEnd_8341434 := by exact prefixLift 8341434
  have htrace : WordTrace (prefixWord ++ tailWord_8341434) baseStart_8341434 baseEnd_8341434 := by
    simpa [prefixWord, tailWord_8341434, baseEnd_8341434] using wordTrace_append hprefix tailTrace_8341434
  have hstable : (prefixWord ++ tailWord_8341434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341434).length < 2 ^ (prefixWord ++ tailWord_8341434).sum := by decide
  have hdescent : baseEnd_8341434 < baseStart_8341434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341458 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_8341458 : Nat := 118140960795 + 8341458 * 2 ^ 59
def prefixEnd_8341458 : Nat := 4983230072969 + 3 ^ 40 * 8341458 * 2
def baseEnd_8341458 : Nat := 4283177313291730240913339

theorem tailTrace_8341458 : CollatzResearch.WordTrace tailWord_8341458 prefixEnd_8341458 4283177313291730240913339 := by
  unfold tailWord_8341458
  simp only [CollatzResearch.WordTrace]
  refine ⟨76059491853582437113176257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202825311609553165635136685 76059491853582437113176257)
  ·
    refine ⟨57044618890186827834882193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76059491853582437113176257 57044618890186827834882193)
    ·
      refine ⟨42783464167640120876161645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57044618890186827834882193 42783464167640120876161645)
      ·
        refine ⟨16043799062865045328560617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42783464167640120876161645 16043799062865045328560617)
        ·
          refine ⟨12032849297148783996420463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16043799062865045328560617 12032849297148783996420463)
          ·
            refine ⟨18049273945723175994630695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12032849297148783996420463 18049273945723175994630695)
            ·
              refine ⟨27073910918584763991946043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18049273945723175994630695 27073910918584763991946043)
              ·
                refine ⟨40610866377877145987919065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27073910918584763991946043 40610866377877145987919065)
                ·
                  refine ⟨30458149783407859490939299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40610866377877145987919065 30458149783407859490939299)
                  ·
                    refine ⟨45687224675111789236408949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30458149783407859490939299 45687224675111789236408949)
                    ·
                      refine ⟨4283177313291730240913339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45687224675111789236408949 4283177313291730240913339)
                      ·
                        rfl

theorem cell23_8341458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_8341458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341458 prefixEnd_8341458 := by exact prefixLift 8341458
  have htrace : WordTrace (prefixWord ++ tailWord_8341458) baseStart_8341458 baseEnd_8341458 := by
    simpa [prefixWord, tailWord_8341458, baseEnd_8341458] using wordTrace_append hprefix tailTrace_8341458
  have hstable : (prefixWord ++ tailWord_8341458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341458).length < 2 ^ (prefixWord ++ tailWord_8341458).sum := by decide
  have hdescent : baseEnd_8341458 < baseStart_8341458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341489 : List Nat := [1, 2, 2, 2, 5, 2, 2, 1, 2, 2, 2]
def baseStart_8341489 : Nat := 118140960795 + 8341489 * 2 ^ 59
def prefixEnd_8341489 : Nat := 4983230072969 + 3 ^ 40 * 8341489 * 2
def baseEnd_8341489 : Nat := 4283193231192019619625697

theorem tailTrace_8341489 : CollatzResearch.WordTrace tailWord_8341489 prefixEnd_8341489 4283193231192019619625697 := by
  unfold tailWord_8341489
  simp only [CollatzResearch.WordTrace]
  refine ⟨304239098077217440747083521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202826065384811627164722347 304239098077217440747083521)
  ·
    refine ⟨228179323557913080560312641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304239098077217440747083521 228179323557913080560312641)
    ·
      refine ⟨171134492668434810420234481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228179323557913080560312641 171134492668434810420234481)
      ·
        refine ⟨128350869501326107815175861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171134492668434810420234481 128350869501326107815175861)
        ·
          refine ⟨12032894015749322607672737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128350869501326107815175861 12032894015749322607672737)
          ·
            refine ⟨9024670511811991955754553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12032894015749322607672737 9024670511811991955754553)
            ·
              refine ⟨6768502883858993966815915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9024670511811991955754553 6768502883858993966815915)
              ·
                refine ⟨10152754325788490950223873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768502883858993966815915 10152754325788490950223873)
                ·
                  refine ⟨7614565744341368212667905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10152754325788490950223873 7614565744341368212667905)
                  ·
                    refine ⟨5710924308256026159500929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7614565744341368212667905 5710924308256026159500929)
                    ·
                      refine ⟨4283193231192019619625697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5710924308256026159500929 4283193231192019619625697)
                      ·
                        rfl

theorem cell23_8341489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_8341489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341489 prefixEnd_8341489 := by exact prefixLift 8341489
  have htrace : WordTrace (prefixWord ++ tailWord_8341489) baseStart_8341489 baseEnd_8341489 := by
    simpa [prefixWord, tailWord_8341489, baseEnd_8341489] using wordTrace_append hprefix tailTrace_8341489
  have hstable : (prefixWord ++ tailWord_8341489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341489).length < 2 ^ (prefixWord ++ tailWord_8341489).sum := by decide
  have hdescent : baseEnd_8341489 < baseStart_8341489 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341528 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 2, 4, 2]
def baseStart_8341528 : Nat := 118140960795 + 8341528 * 2 ^ 59
def prefixEnd_8341528 : Nat := 4983230072969 + 3 ^ 40 * 8341528 * 2
def baseEnd_8341528 : Nat := 4283213256937544967038017

theorem tailTrace_8341528 : CollatzResearch.WordTrace tailWord_8341528 prefixEnd_8341528 4283213256937544967038017 := by
  unfold tailWord_8341528
  simp only [CollatzResearch.WordTrace]
  refine ⟨152120260262038075203876619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202827013682717433605168825 152120260262038075203876619)
  ·
    refine ⟨228180390393057112805814929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152120260262038075203876619 228180390393057112805814929)
    ·
      refine ⟨171135292794792834604361197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228180390393057112805814929 171135292794792834604361197)
      ·
        refine ⟨64175734798047312976635449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171135292794792834604361197 64175734798047312976635449)
        ·
          refine ⟨48131801098535484732476587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64175734798047312976635449 48131801098535484732476587)
          ·
            refine ⟨72197701647803227098714881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48131801098535484732476587 72197701647803227098714881)
            ·
              refine ⟨54148276235852420324036161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72197701647803227098714881 54148276235852420324036161)
              ·
                refine ⟨40611207176889315243027121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54148276235852420324036161 40611207176889315243027121)
                ·
                  refine ⟨30458405382666986432270341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40611207176889315243027121 30458405382666986432270341)
                  ·
                    refine ⟨5710951009250059956050689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30458405382666986432270341 5710951009250059956050689)
                    ·
                      refine ⟨4283213256937544967038017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5710951009250059956050689 4283213256937544967038017)
                      ·
                        rfl

theorem cell23_8341528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_8341528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341528 prefixEnd_8341528 := by exact prefixLift 8341528
  have htrace : WordTrace (prefixWord ++ tailWord_8341528) baseStart_8341528 baseEnd_8341528 := by
    simpa [prefixWord, tailWord_8341528, baseEnd_8341528] using wordTrace_append hprefix tailTrace_8341528
  have hstable : (prefixWord ++ tailWord_8341528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341528).length < 2 ^ (prefixWord ++ tailWord_8341528).sum := by decide
  have hdescent : baseEnd_8341528 < baseStart_8341528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341531 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 3]
def baseStart_8341531 : Nat := 118140960795 + 8341531 * 2 ^ 59
def prefixEnd_8341531 : Nat := 4983230072969 + 3 ^ 40 * 8341531 * 2
def baseEnd_8341531 : Nat := 4283214797379508455300503

theorem tailTrace_8341531 : CollatzResearch.WordTrace tailWord_8341531 prefixEnd_8341531 4283214797379508455300503 := by
  unfold tailWord_8341531
  simp only [CollatzResearch.WordTrace]
  refine ⟨304240629943065281920112447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202827086628710187946741631 304240629943065281920112447)
  ·
    refine ⟨456360944914597922880168671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304240629943065281920112447 456360944914597922880168671)
    ·
      refine ⟨684541417371896884320253007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456360944914597922880168671 684541417371896884320253007)
      ·
        refine ⟨1026812126057845326480379511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684541417371896884320253007 1026812126057845326480379511)
        ·
          refine ⟨1540218189086767989720569267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026812126057845326480379511 1540218189086767989720569267)
          ·
            refine ⟨2310327283630151984580853901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540218189086767989720569267 2310327283630151984580853901)
            ·
              refine ⟨866372731361306994217820213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2310327283630151984580853901 866372731361306994217820213)
              ·
                refine ⟨81222443565122530707920645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 866372731361306994217820213 81222443565122530707920645)
                ·
                  refine ⟨15229208168460474507735121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81222443565122530707920645 15229208168460474507735121)
                  ·
                    refine ⟨11421906126345355880801341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15229208168460474507735121 11421906126345355880801341)
                    ·
                      refine ⟨4283214797379508455300503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11421906126345355880801341 4283214797379508455300503)
                      ·
                        rfl

theorem cell23_8341531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 3].length) (baseStart_8341531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341531 prefixEnd_8341531 := by exact prefixLift 8341531
  have htrace : WordTrace (prefixWord ++ tailWord_8341531) baseStart_8341531 baseEnd_8341531 := by
    simpa [prefixWord, tailWord_8341531, baseEnd_8341531] using wordTrace_append hprefix tailTrace_8341531
  have hstable : (prefixWord ++ tailWord_8341531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341531).length < 2 ^ (prefixWord ++ tailWord_8341531).sum := by decide
  have hdescent : baseEnd_8341531 < baseStart_8341531 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341538 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_8341538 : Nat := 118140960795 + 8341538 * 2 ^ 59
def prefixEnd_8341538 : Nat := 4983230072969 + 3 ^ 40 * 8341538 * 2
def baseEnd_8341538 : Nat := 1427739463914696642637657

theorem tailTrace_8341538 : CollatzResearch.WordTrace tailWord_8341538 prefixEnd_8341538 1427739463914696642637657 := by
  unfold tailWord_8341538
  simp only [CollatzResearch.WordTrace]
  refine ⟨76060221313509980528904317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202827256836026614743744845 76060221313509980528904317)
  ·
    refine ⟨28522582992566242698339119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76060221313509980528904317 28522582992566242698339119)
    ·
      refine ⟨42783874488849364047508679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28522582992566242698339119 42783874488849364047508679)
      ·
        refine ⟨64175811733274046071263019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42783874488849364047508679 64175811733274046071263019)
        ·
          refine ⟨96263717599911069106894529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64175811733274046071263019 96263717599911069106894529)
          ·
            refine ⟨72197788199933301830170897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96263717599911069106894529 72197788199933301830170897)
            ·
              refine ⟨54148341149949976372628173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72197788199933301830170897 54148341149949976372628173)
              ·
                refine ⟨20305627931231241139735565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54148341149949976372628173 20305627931231241139735565)
                ·
                  refine ⟨7614610474211715427400837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20305627931231241139735565 7614610474211715427400837)
                  ·
                    refine ⟨1427739463914696642637657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7614610474211715427400837 1427739463914696642637657)
                    ·
                      rfl

theorem cell23_8341538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_8341538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341538 prefixEnd_8341538 := by exact prefixLift 8341538
  have htrace : WordTrace (prefixWord ++ tailWord_8341538) baseStart_8341538 baseEnd_8341538 := by
    simpa [prefixWord, tailWord_8341538, baseEnd_8341538] using wordTrace_append hprefix tailTrace_8341538
  have hstable : (prefixWord ++ tailWord_8341538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341538).length < 2 ^ (prefixWord ++ tailWord_8341538).sum := by decide
  have hdescent : baseEnd_8341538 < baseStart_8341538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341578 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_8341578 : Nat := 118140960795 + 8341578 * 2 ^ 59
def prefixEnd_8341578 : Nat := 4983230072969 + 3 ^ 40 * 8341578 * 2
def baseEnd_8341578 : Nat := 4283238930970269771412787

theorem tailTrace_8341578 : CollatzResearch.WordTrace tailWord_8341578 prefixEnd_8341578 4283238930970269771412787 := by
  unfold tailWord_8341578
  simp only [CollatzResearch.WordTrace]
  refine ⟨76060586043473752236768347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202828229449263339298048925 76060586043473752236768347)
  ·
    refine ⟨114090879065210628355152521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76060586043473752236768347 114090879065210628355152521)
    ·
      refine ⟨85568159298907971266364391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114090879065210628355152521 85568159298907971266364391)
      ·
        refine ⟨128352238948361956899546587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85568159298907971266364391 128352238948361956899546587)
        ·
          refine ⟨192528358422542935349319881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128352238948361956899546587 192528358422542935349319881)
          ·
            refine ⟨144396268816907201511989911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192528358422542935349319881 144396268816907201511989911)
            ·
              refine ⟨216594403225360802267984867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144396268816907201511989911 216594403225360802267984867)
              ·
                refine ⟨324891604838041203401977301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216594403225360802267984867 324891604838041203401977301)
                ·
                  refine ⟨7614646988391590704733843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 324891604838041203401977301 7614646988391590704733843)
                  ·
                    refine ⟨11421970482587386057100765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7614646988391590704733843 11421970482587386057100765)
                    ·
                      refine ⟨4283238930970269771412787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11421970482587386057100765 4283238930970269771412787)
                      ·
                        rfl

theorem cell23_8341578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_8341578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341578 prefixEnd_8341578 := by exact prefixLift 8341578
  have htrace : WordTrace (prefixWord ++ tailWord_8341578) baseStart_8341578 baseEnd_8341578 := by
    simpa [prefixWord, tailWord_8341578, baseEnd_8341578] using wordTrace_append hprefix tailTrace_8341578
  have hstable : (prefixWord ++ tailWord_8341578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341578).length < 2 ^ (prefixWord ++ tailWord_8341578).sum := by decide
  have hdescent : baseEnd_8341578 < baseStart_8341578 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341602 : List Nat := [3, 3, 2, 2, 2, 1, 3, 1, 6]
def baseStart_8341602 : Nat := 118140960795 + 8341602 * 2 ^ 59
def prefixEnd_8341602 : Nat := 4983230072969 + 3 ^ 40 * 8341602 * 2
def baseEnd_8341602 : Nat := 475916806056219741945853

theorem tailTrace_8341602 : CollatzResearch.WordTrace tailWord_8341602 prefixEnd_8341602 475916806056219741945853 := by
  unfold tailWord_8341602
  simp only [CollatzResearch.WordTrace]
  refine ⟨76060804881452015261486765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202828813017205374030631373 76060804881452015261486765)
  ·
    refine ⟨28522801830544505723057537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76060804881452015261486765 28522801830544505723057537)
    ·
      refine ⟨21392101372908379292293153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28522801830544505723057537 21392101372908379292293153)
      ·
        refine ⟨16044076029681284469219865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21392101372908379292293153 16044076029681284469219865)
        ·
          refine ⟨12033057022260963351914899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16044076029681284469219865 12033057022260963351914899)
          ·
            refine ⟨18049585533391445027872349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12033057022260963351914899 18049585533391445027872349)
            ·
              refine ⟨6768594575021791885452131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18049585533391445027872349 6768594575021791885452131)
              ·
                refine ⟨10152891862532687828178197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768594575021791885452131 10152891862532687828178197)
                ·
                  refine ⟨475916806056219741945853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10152891862532687828178197 475916806056219741945853)
                  ·
                    rfl

theorem cell23_8341602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_8341602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341602 prefixEnd_8341602 := by exact prefixLift 8341602
  have htrace : WordTrace (prefixWord ++ tailWord_8341602) baseStart_8341602 baseEnd_8341602 := by
    simpa [prefixWord, tailWord_8341602, baseEnd_8341602] using wordTrace_append hprefix tailTrace_8341602
  have hstable : (prefixWord ++ tailWord_8341602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341602).length < 2 ^ (prefixWord ++ tailWord_8341602).sum := by decide
  have hdescent : baseEnd_8341602 < baseStart_8341602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341628 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 4, 4]
def baseStart_8341628 : Nat := 118140960795 + 8341628 * 2 ^ 59
def prefixEnd_8341628 : Nat := 4983230072969 + 3 ^ 40 * 8341628 * 2
def baseEnd_8341628 : Nat := 1427754868334331525262519

theorem tailTrace_8341628 : CollatzResearch.WordTrace tailWord_8341628 prefixEnd_8341628 1427754868334331525262519 := by
  unfold tailWord_8341628
  simp only [CollatzResearch.WordTrace]
  refine ⟨152122083911856933743196769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202829445215809244990929025 152122083911856933743196769)
  ·
    refine ⟨114091562933892700307397577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152122083911856933743196769 114091562933892700307397577)
    ·
      refine ⟨85568672200419525230548183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114091562933892700307397577 85568672200419525230548183)
      ·
        refine ⟨128353008300629287845822275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85568672200419525230548183 128353008300629287845822275)
        ·
          refine ⟨192529512450943931768733413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128353008300629287845822275 192529512450943931768733413)
          ·
            refine ⟨36099283584551987206637515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192529512450943931768733413 36099283584551987206637515)
            ·
              refine ⟨54148925376827980809956273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36099283584551987206637515 54148925376827980809956273)
              ·
                refine ⟨40611694032620985607467205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54148925376827980809956273 40611694032620985607467205)
                ·
                  refine ⟨7614692631116434801400101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40611694032620985607467205 7614692631116434801400101)
                  ·
                    refine ⟨1427754868334331525262519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7614692631116434801400101 1427754868334331525262519)
                    ·
                      rfl

theorem cell23_8341628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_8341628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341628 prefixEnd_8341628 := by exact prefixLift 8341628
  have htrace : WordTrace (prefixWord ++ tailWord_8341628) baseStart_8341628 baseEnd_8341628 := by
    simpa [prefixWord, tailWord_8341628, baseEnd_8341628] using wordTrace_append hprefix tailTrace_8341628
  have hstable : (prefixWord ++ tailWord_8341628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341628).length < 2 ^ (prefixWord ++ tailWord_8341628).sum := by decide
  have hdescent : baseEnd_8341628 < baseStart_8341628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341629 : List Nat := [1, 4, 1, 1, 3, 4, 1, 3, 1, 1, 3]
def baseStart_8341629 : Nat := 118140960795 + 8341629 * 2 ^ 59
def prefixEnd_8341629 : Nat := 4983230072969 + 3 ^ 40 * 8341629 * 2
def baseEnd_8341629 : Nat := 4283265118483649071875053

theorem tailTrace_8341629 : CollatzResearch.WordTrace tailWord_8341629 prefixEnd_8341629 4283265118483649071875053 := by
  unfold tailWord_8341629
  simp only [CollatzResearch.WordTrace]
  refine ⟨304244204296710244657179941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202829469531140163104786627 304244204296710244657179941)
  ·
    refine ⟨57045788305633170873221239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304244204296710244657179941 57045788305633170873221239)
    ·
      refine ⟨85568682458449756309831859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57045788305633170873221239 85568682458449756309831859)
      ·
        refine ⟨128353023687674634464747789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85568682458449756309831859 128353023687674634464747789)
        ·
          refine ⟨48132383882877987924280421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128353023687674634464747789 48132383882877987924280421)
          ·
            refine ⟨9024821978039622735802579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48132383882877987924280421 9024821978039622735802579)
            ·
              refine ⟨13537232967059434103703869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9024821978039622735802579 13537232967059434103703869)
              ·
                refine ⟨5076462362647287788888951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13537232967059434103703869 5076462362647287788888951)
                ·
                  refine ⟨7614693543970931683333427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076462362647287788888951 7614693543970931683333427)
                  ·
                    refine ⟨11422040315956397525000141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7614693543970931683333427 11422040315956397525000141)
                    ·
                      refine ⟨4283265118483649071875053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11422040315956397525000141 4283265118483649071875053)
                      ·
                        rfl

theorem cell23_8341629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_8341629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341629 prefixEnd_8341629 := by exact prefixLift 8341629
  have htrace : WordTrace (prefixWord ++ tailWord_8341629) baseStart_8341629 baseEnd_8341629 := by
    simpa [prefixWord, tailWord_8341629, baseEnd_8341629] using wordTrace_append hprefix tailTrace_8341629
  have hstable : (prefixWord ++ tailWord_8341629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341629).length < 2 ^ (prefixWord ++ tailWord_8341629).sum := by decide
  have hdescent : baseEnd_8341629 < baseStart_8341629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341646 : List Nat := [4, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3]
def baseStart_8341646 : Nat := 118140960795 + 8341646 * 2 ^ 59
def prefixEnd_8341646 : Nat := 4983230072969 + 3 ^ 40 * 8341646 * 2
def baseEnd_8341646 : Nat := 4283273847654775505362475

theorem tailTrace_8341646 : CollatzResearch.WordTrace tailWord_8341646 prefixEnd_8341646 4283273847654775505362475 := by
  unfold tailWord_8341646
  simp only [CollatzResearch.WordTrace]
  refine ⟨38030603042206082070068599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202829882891765771040365861 38030603042206082070068599)
  ·
    refine ⟨57045904563309123105102899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38030603042206082070068599 57045904563309123105102899)
    ·
      refine ⟨85568856844963684657654349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57045904563309123105102899 85568856844963684657654349)
      ·
        refine ⟨32088321316861381746620381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85568856844963684657654349 32088321316861381746620381)
        ·
          refine ⟨12033120493823018154982643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32088321316861381746620381 12033120493823018154982643)
          ·
            refine ⟨18049680740734527232473965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12033120493823018154982643 18049680740734527232473965)
            ·
              refine ⟨6768630277775447712177737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18049680740734527232473965 6768630277775447712177737)
              ·
                refine ⟨5076472708331585784133303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6768630277775447712177737 5076472708331585784133303)
                ·
                  refine ⟨7614709062497378676199955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076472708331585784133303 7614709062497378676199955)
                  ·
                    refine ⟨11422063593746068014299933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7614709062497378676199955 11422063593746068014299933)
                    ·
                      refine ⟨4283273847654775505362475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11422063593746068014299933 4283273847654775505362475)
                      ·
                        rfl

theorem cell23_8341646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_8341646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341646 prefixEnd_8341646 := by exact prefixLift 8341646
  have htrace : WordTrace (prefixWord ++ tailWord_8341646) baseStart_8341646 baseEnd_8341646 := by
    simpa [prefixWord, tailWord_8341646, baseEnd_8341646] using wordTrace_append hprefix tailTrace_8341646
  have hstable : (prefixWord ++ tailWord_8341646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341646).length < 2 ^ (prefixWord ++ tailWord_8341646).sum := by decide
  have hdescent : baseEnd_8341646 < baseStart_8341646 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341728 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 3]
def baseStart_8341728 : Nat := 118140960795 + 8341728 * 2 ^ 59
def prefixEnd_8341728 : Nat := 4983230072969 + 3 ^ 40 * 8341728 * 2
def baseEnd_8341728 : Nat := 4283315953068444184537097

theorem tailTrace_8341728 : CollatzResearch.WordTrace tailWord_8341728 prefixEnd_8341728 4283315953068444184537097 := by
  unfold tailWord_8341728
  simp only [CollatzResearch.WordTrace]
  refine ⟨152123907561675792282516919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202831876748901056376689225 152123907561675792282516919)
  ·
    refine ⟨228185861342513688423775379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152123907561675792282516919 228185861342513688423775379)
    ·
      refine ⟨342278792013770532635663069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228185861342513688423775379 342278792013770532635663069)
      ·
        refine ⟨128354547005163949738373651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342278792013770532635663069 128354547005163949738373651)
        ·
          refine ⟨192531820507745924607560477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128354547005163949738373651 192531820507745924607560477)
          ·
            refine ⟨72199432690404721727835179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192531820507745924607560477 72199432690404721727835179)
            ·
              refine ⟨108299149035607082591752769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72199432690404721727835179 108299149035607082591752769)
              ·
                refine ⟨81224361776705311943814577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108299149035607082591752769 81224361776705311943814577)
                ·
                  refine ⟨60918271332528983957860933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81224361776705311943814577 60918271332528983957860933)
                  ·
                    refine ⟨11422175874849184492098925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60918271332528983957860933 11422175874849184492098925)
                    ·
                      refine ⟨4283315953068444184537097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11422175874849184492098925 4283315953068444184537097)
                      ·
                        rfl

theorem cell23_8341728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_8341728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341728 prefixEnd_8341728 := by exact prefixLift 8341728
  have htrace : WordTrace (prefixWord ++ tailWord_8341728) baseStart_8341728 baseEnd_8341728 := by
    simpa [prefixWord, tailWord_8341728, baseEnd_8341728] using wordTrace_append hprefix tailTrace_8341728
  have hstable : (prefixWord ++ tailWord_8341728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341728).length < 2 ^ (prefixWord ++ tailWord_8341728).sum := by decide
  have hdescent : baseEnd_8341728 < baseStart_8341728 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341738 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_8341738 : Nat := 118140960795 + 8341738 * 2 ^ 59
def prefixEnd_8341738 : Nat := 4983230072969 + 3 ^ 40 * 8341738 * 2
def baseEnd_8341738 : Nat := 4283321087874989145412051

theorem tailTrace_8341738 : CollatzResearch.WordTrace tailWord_8341738 prefixEnd_8341738 4283321087874989145412051 := by
  unfold tailWord_8341738
  simp only [CollatzResearch.WordTrace]
  refine ⟨76062044963328839068224467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202832119902210237515265245 76062044963328839068224467)
  ·
    refine ⟨114093067444993258602336701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76062044963328839068224467 114093067444993258602336701)
    ·
      refine ⟨42784900291872471975876263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114093067444993258602336701 42784900291872471975876263)
      ·
        refine ⟨64177350437808707963814395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42784900291872471975876263 64177350437808707963814395)
        ·
          refine ⟨96266025656713061945721593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64177350437808707963814395 96266025656713061945721593)
          ·
            refine ⟨72199519242534796459291195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96266025656713061945721593 72199519242534796459291195)
            ·
              refine ⟨108299278863802194688936793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72199519242534796459291195 108299278863802194688936793)
              ·
                refine ⟨81224459147851646016702595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108299278863802194688936793 81224459147851646016702595)
                ·
                  refine ⟨121836688721777469025053893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81224459147851646016702595 121836688721777469025053893)
                  ·
                    refine ⟨22844379135333275442197605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121836688721777469025053893 22844379135333275442197605)
                    ·
                      refine ⟨4283321087874989145412051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22844379135333275442197605 4283321087874989145412051)
                      ·
                        rfl

theorem cell23_8341738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_8341738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341738 prefixEnd_8341738 := by exact prefixLift 8341738
  have htrace : WordTrace (prefixWord ++ tailWord_8341738) baseStart_8341738 baseEnd_8341738 := by
    simpa [prefixWord, tailWord_8341738, baseEnd_8341738] using wordTrace_append hprefix tailTrace_8341738
  have hstable : (prefixWord ++ tailWord_8341738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341738).length < 2 ^ (prefixWord ++ tailWord_8341738).sum := by decide
  have hdescent : baseEnd_8341738 < baseStart_8341738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341742 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_8341742 : Nat := 118140960795 + 8341742 * 2 ^ 59
def prefixEnd_8341742 : Nat := 4983230072969 + 3 ^ 40 * 8341742 * 2
def baseEnd_8341742 : Nat := 4283323141797607129762033

theorem tailTrace_8341742 : CollatzResearch.WordTrace tailWord_8341742 prefixEnd_8341742 4283323141797607129762033 := by
  unfold tailWord_8341742
  simp only [CollatzResearch.WordTrace]
  refine ⟨38031040718162608119505435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202832217163533909970695653 38031040718162608119505435)
  ·
    refine ⟨57046561077243912179258153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38031040718162608119505435 57046561077243912179258153)
    ·
      refine ⟨42784920807932934134443615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57046561077243912179258153 42784920807932934134443615)
      ·
        refine ⟨64177381211899401201665423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42784920807932934134443615 64177381211899401201665423)
        ·
          refine ⟨96266071817849101802498135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64177381211899401201665423 96266071817849101802498135)
          ·
            refine ⟨144399107726773652703747203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96266071817849101802498135 144399107726773652703747203)
            ·
              refine ⟨216598661590160479055620805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144399107726773652703747203 216598661590160479055620805)
              ·
                refine ⟨40612249048155089822928901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216598661590160479055620805 40612249048155089822928901)
                ·
                  refine ⟨7614796696529079341799169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40612249048155089822928901 7614796696529079341799169)
                  ·
                    refine ⟨5711097522396809506349377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7614796696529079341799169 5711097522396809506349377)
                    ·
                      refine ⟨4283323141797607129762033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711097522396809506349377 4283323141797607129762033)
                      ·
                        rfl

theorem cell23_8341742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_8341742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341742 prefixEnd_8341742 := by exact prefixLift 8341742
  have htrace : WordTrace (prefixWord ++ tailWord_8341742) baseStart_8341742 baseEnd_8341742 := by
    simpa [prefixWord, tailWord_8341742, baseEnd_8341742] using wordTrace_append hprefix tailTrace_8341742
  have hstable : (prefixWord ++ tailWord_8341742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341742).length < 2 ^ (prefixWord ++ tailWord_8341742).sum := by decide
  have hdescent : baseEnd_8341742 < baseStart_8341742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341746 : List Nat := [3, 2, 1, 3, 2, 3, 2, 1, 1, 3, 2]
def baseStart_8341746 : Nat := 118140960795 + 8341746 * 2 ^ 59
def prefixEnd_8341746 : Nat := 4983230072969 + 3 ^ 40 * 8341746 * 2
def baseEnd_8341746 : Nat := 4283325195720225114112015

theorem tailTrace_8341746 : CollatzResearch.WordTrace tailWord_8341746 prefixEnd_8341746 4283325195720225114112015 := by
  unfold tailWord_8341746
  simp only [CollatzResearch.WordTrace]
  refine ⟨76062117909321593409797273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202832314424857582426126061 76062117909321593409797273)
  ·
    refine ⟨57046588431991195057347955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76062117909321593409797273 57046588431991195057347955)
    ·
      refine ⟨85569882647986792586021933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57046588431991195057347955 85569882647986792586021933)
      ·
        refine ⟨32088705992995047219758225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85569882647986792586021933 32088705992995047219758225)
        ·
          refine ⟨24066529494746285414818669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32088705992995047219758225 24066529494746285414818669)
          ·
            refine ⟨9024948560529857030557001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24066529494746285414818669 9024948560529857030557001)
            ·
              refine ⟨6768711420397392772917751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9024948560529857030557001 6768711420397392772917751)
              ·
                refine ⟨10153067130596089159376627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768711420397392772917751 10153067130596089159376627)
                ·
                  refine ⟨15229600695894133739064941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10153067130596089159376627 15229600695894133739064941)
                  ·
                    refine ⟨5711100260960300152149353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15229600695894133739064941 5711100260960300152149353)
                    ·
                      refine ⟨4283325195720225114112015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711100260960300152149353 4283325195720225114112015)
                      ·
                        rfl

theorem cell23_8341746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_8341746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341746 prefixEnd_8341746 := by exact prefixLift 8341746
  have htrace : WordTrace (prefixWord ++ tailWord_8341746) baseStart_8341746 baseEnd_8341746 := by
    simpa [prefixWord, tailWord_8341746, baseEnd_8341746] using wordTrace_append hprefix tailTrace_8341746
  have hstable : (prefixWord ++ tailWord_8341746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341746).length < 2 ^ (prefixWord ++ tailWord_8341746).sum := by decide
  have hdescent : baseEnd_8341746 < baseStart_8341746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341788 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_8341788 : Nat := 118140960795 + 8341788 * 2 ^ 59
def prefixEnd_8341788 : Nat := 4983230072969 + 3 ^ 40 * 8341788 * 2
def baseEnd_8341788 : Nat := 4283346761907713949786821

theorem tailTrace_8341788 : CollatzResearch.WordTrace tailWord_8341788 prefixEnd_8341788 4283346761907713949786821 := by
  unfold tailWord_8341788
  simp only [CollatzResearch.WordTrace]
  refine ⟨152125001751567107406109009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202833335668756143208145345 152125001751567107406109009)
  ·
    refine ⟨114093751313675330554581757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152125001751567107406109009 114093751313675330554581757)
    ·
      refine ⟨42785156742628248957968159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114093751313675330554581757 42785156742628248957968159)
      ·
        refine ⟨64177735113942373436952239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42785156742628248957968159 64177735113942373436952239)
        ·
          refine ⟨96266602670913560155428359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64177735113942373436952239 96266602670913560155428359)
          ·
            refine ⟨144399904006370340233142539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96266602670913560155428359 144399904006370340233142539)
            ·
              refine ⟨216599856009555510349713809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144399904006370340233142539 216599856009555510349713809)
              ·
                refine ⟨162449892007166632762285357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216599856009555510349713809 162449892007166632762285357)
                ·
                  refine ⟨60918709502687487285857009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162449892007166632762285357 60918709502687487285857009)
                  ·
                    refine ⟨45689032127015615464392757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60918709502687487285857009 45689032127015615464392757)
                    ·
                      refine ⟨4283346761907713949786821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45689032127015615464392757 4283346761907713949786821)
                      ·
                        rfl

theorem cell23_8341788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_8341788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341788 prefixEnd_8341788 := by exact prefixLift 8341788
  have htrace : WordTrace (prefixWord ++ tailWord_8341788) baseStart_8341788 baseEnd_8341788 := by
    simpa [prefixWord, tailWord_8341788, baseEnd_8341788] using wordTrace_append hprefix tailTrace_8341788
  have hstable : (prefixWord ++ tailWord_8341788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341788).length < 2 ^ (prefixWord ++ tailWord_8341788).sum := by decide
  have hdescent : baseEnd_8341788 < baseStart_8341788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341812 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_8341812 : Nat := 118140960795 + 8341812 * 2 ^ 59
def prefixEnd_8341812 : Nat := 4983230072969 + 3 ^ 40 * 8341812 * 2
def baseEnd_8341812 : Nat := 1427786361814473951962237

theorem tailTrace_8341812 : CollatzResearch.WordTrace tailWord_8341812 prefixEnd_8341812 1427786361814473951962237 := by
  unfold tailWord_8341812
  simp only [CollatzResearch.WordTrace]
  refine ⟨152125439427523633455545845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202833919236698177940727793 152125439427523633455545845)
  ·
    refine ⟨14261759946330340636457423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152125439427523633455545845 14261759946330340636457423)
    ·
      refine ⟨21392639919495510954686135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14261759946330340636457423 21392639919495510954686135)
      ·
        refine ⟨32088959879243266432029203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21392639919495510954686135 32088959879243266432029203)
        ·
          refine ⟨48133439818864899648043805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32088959879243266432029203 48133439818864899648043805)
          ·
            refine ⟨18050039932074337368016427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48133439818864899648043805 18050039932074337368016427)
            ·
              refine ⟨27075059898111506052024641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18050039932074337368016427 27075059898111506052024641)
              ·
                refine ⟨20306294923583629539018481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27075059898111506052024641 20306294923583629539018481)
                ·
                  refine ⟨15229721192687722154263861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20306294923583629539018481 15229721192687722154263861)
                  ·
                    refine ⟨1427786361814473951962237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15229721192687722154263861 1427786361814473951962237)
                    ·
                      rfl

theorem cell23_8341812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_8341812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341812 prefixEnd_8341812 := by exact prefixLift 8341812
  have htrace : WordTrace (prefixWord ++ tailWord_8341812) baseStart_8341812 baseEnd_8341812 := by
    simpa [prefixWord, tailWord_8341812, baseEnd_8341812] using wordTrace_append hprefix tailTrace_8341812
  have hstable : (prefixWord ++ tailWord_8341812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341812).length < 2 ^ (prefixWord ++ tailWord_8341812).sum := by decide
  have hdescent : baseEnd_8341812 < baseStart_8341812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341815 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 4, 4, 2]
def baseStart_8341815 : Nat := 118140960795 + 8341815 * 2 ^ 59
def prefixEnd_8341815 : Nat := 4983230072969 + 3 ^ 40 * 8341815 * 2
def baseEnd_8341815 : Nat := 4283360625885385344149197

theorem tailTrace_8341815 : CollatzResearch.WordTrace tailWord_8341815 prefixEnd_8341815 4283360625885385344149197 := by
  unfold tailWord_8341815
  simp only [CollatzResearch.WordTrace]
  refine ⟨304250988274036398423450899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202833992182690932282300599 304250988274036398423450899)
  ·
    refine ⟨456376482411054597635176349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304250988274036398423450899 456376482411054597635176349)
    ·
      refine ⟨171141180904145474113191131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456376482411054597635176349 171141180904145474113191131)
      ·
        refine ⟨256711771356218211169786697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171141180904145474113191131 256711771356218211169786697)
        ·
          refine ⟨192533828517163658377340023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256711771356218211169786697 192533828517163658377340023)
          ·
            refine ⟨288800742775745487566010035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192533828517163658377340023 288800742775745487566010035)
            ·
              refine ⟨433201114163618231349015053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288800742775745487566010035 433201114163618231349015053)
              ·
                refine ⟨162450417811356836755880645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433201114163618231349015053 162450417811356836755880645)
                ·
                  refine ⟨30459453339629406891727621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162450417811356836755880645 30459453339629406891727621)
                  ·
                    refine ⟨5711147501180513792198929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30459453339629406891727621 5711147501180513792198929)
                    ·
                      refine ⟨4283360625885385344149197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711147501180513792198929 4283360625885385344149197)
                      ·
                        rfl

theorem cell23_8341815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 4, 2].length) (baseStart_8341815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341815 prefixEnd_8341815 := by exact prefixLift 8341815
  have htrace : WordTrace (prefixWord ++ tailWord_8341815) baseStart_8341815 baseEnd_8341815 := by
    simpa [prefixWord, tailWord_8341815, baseEnd_8341815] using wordTrace_append hprefix tailTrace_8341815
  have hstable : (prefixWord ++ tailWord_8341815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341815).length < 2 ^ (prefixWord ++ tailWord_8341815).sum := by decide
  have hdescent : baseEnd_8341815 < baseStart_8341815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341838 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 10]
def baseStart_8341838 : Nat := 118140960795 + 8341838 * 2 ^ 59
def prefixEnd_8341838 : Nat := 4983230072969 + 3 ^ 40 * 8341838 * 2
def baseEnd_8341838 : Nat := 475930270660048750462399

theorem tailTrace_8341838 : CollatzResearch.WordTrace tailWord_8341838 prefixEnd_8341838 475930270660048750462399 := by
  unfold tailWord_8341838
  simp only [CollatzResearch.WordTrace]
  refine ⟨38031478394119134168942271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202834551435302048901025445 38031478394119134168942271)
  ·
    refine ⟨57047217591178701253413407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38031478394119134168942271 57047217591178701253413407)
    ·
      refine ⟨85570826386768051880120111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57047217591178701253413407 85570826386768051880120111)
      ·
        refine ⟨128356239580152077820180167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85570826386768051880120111 128356239580152077820180167)
        ·
          refine ⟨192534359370228116730270251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128356239580152077820180167 192534359370228116730270251)
          ·
            refine ⟨288801539055342175095405377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192534359370228116730270251 288801539055342175095405377)
            ·
              refine ⟨216601154291506631321554033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288801539055342175095405377 216601154291506631321554033)
              ·
                refine ⟨162450865718629973491165525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216601154291506631321554033 162450865718629973491165525)
                ·
                  refine ⟨475930270660048750462399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 162450865718629973491165525 475930270660048750462399)
                  ·
                    rfl

theorem cell23_8341838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_8341838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341838 prefixEnd_8341838 := by exact prefixLift 8341838
  have htrace : WordTrace (prefixWord ++ tailWord_8341838) baseStart_8341838 baseEnd_8341838 := by
    simpa [prefixWord, tailWord_8341838, baseEnd_8341838] using wordTrace_append hprefix tailTrace_8341838
  have hstable : (prefixWord ++ tailWord_8341838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341838).length < 2 ^ (prefixWord ++ tailWord_8341838).sum := by decide
  have hdescent : baseEnd_8341838 < baseStart_8341838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341885 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_8341885 : Nat := 118140960795 + 8341885 * 2 ^ 59
def prefixEnd_8341885 : Nat := 4983230072969 + 3 ^ 40 * 8341885 * 2
def baseEnd_8341885 : Nat := 1427798856510400023424625

theorem tailTrace_8341885 : CollatzResearch.WordTrace tailWord_8341885 prefixEnd_8341885 1427798856510400023424625 := by
  unfold tailWord_8341885
  simp only [CollatzResearch.WordTrace]
  refine ⟨304253541383782800378499109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202835694255855200252332739 304253541383782800378499109)
  ·
    refine ⟨57047539009459275070968583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304253541383782800378499109 57047539009459275070968583)
    ·
      refine ⟨85571308514188912606452875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57047539009459275070968583 85571308514188912606452875)
      ·
        refine ⟨128356962771283368909679313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85571308514188912606452875 128356962771283368909679313)
        ·
          refine ⟨96267722078462526682259485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128356962771283368909679313 96267722078462526682259485)
          ·
            refine ⟨36100395779423447505847307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96267722078462526682259485 36100395779423447505847307)
            ·
              refine ⟨54150593669135171258770961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36100395779423447505847307 54150593669135171258770961)
              ·
                refine ⟨40612945251851378444078221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54150593669135171258770961 40612945251851378444078221)
                ·
                  refine ⟨15229854469444266916529333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40612945251851378444078221 15229854469444266916529333)
                  ·
                    refine ⟨1427798856510400023424625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15229854469444266916529333 1427798856510400023424625)
                    ·
                      rfl

theorem cell23_8341885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_8341885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341885 prefixEnd_8341885 := by exact prefixLift 8341885
  have htrace : WordTrace (prefixWord ++ tailWord_8341885) baseStart_8341885 baseEnd_8341885 := by
    simpa [prefixWord, tailWord_8341885, baseEnd_8341885] using wordTrace_append hprefix tailTrace_8341885
  have hstable : (prefixWord ++ tailWord_8341885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341885).length < 2 ^ (prefixWord ++ tailWord_8341885).sum := by decide
  have hdescent : baseEnd_8341885 < baseStart_8341885 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341892 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_8341892 : Nat := 118140960795 + 8341892 * 2 ^ 59
def prefixEnd_8341892 : Nat := 4983230072969 + 3 ^ 40 * 8341892 * 2
def baseEnd_8341892 : Nat := 4283400163895781542886343

theorem tailTrace_8341892 : CollatzResearch.WordTrace tailWord_8341892 prefixEnd_8341892 4283400163895781542886343 := by
  unfold tailWord_8341892
  simp only [CollatzResearch.WordTrace]
  refine ⟨152126898347378720287001965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202835864463171627049335953 152126898347378720287001965)
  ·
    refine ⟨57047586880267020107625737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152126898347378720287001965 57047586880267020107625737)
    ·
      refine ⟨42785690160200265080719303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57047586880267020107625737 42785690160200265080719303)
      ·
        refine ⟨64178535240300397621078955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42785690160200265080719303 64178535240300397621078955)
        ·
          refine ⟨96267802860450596431618433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64178535240300397621078955 96267802860450596431618433)
          ·
            refine ⟨72200852145337947323713825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96267802860450596431618433 72200852145337947323713825)
            ·
              refine ⟨54150639109003460492785369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72200852145337947323713825 54150639109003460492785369)
              ·
                refine ⟨40612979331752595369589027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54150639109003460492785369 40612979331752595369589027)
                ·
                  refine ⟨60919468997628893054383541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40612979331752595369589027 60919468997628893054383541)
                  ·
                    refine ⟨5711200218527708723848457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60919468997628893054383541 5711200218527708723848457)
                    ·
                      refine ⟨4283400163895781542886343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711200218527708723848457 4283400163895781542886343)
                      ·
                        rfl

theorem cell23_8341892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_8341892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341892 prefixEnd_8341892 := by exact prefixLift 8341892
  have htrace : WordTrace (prefixWord ++ tailWord_8341892) baseStart_8341892 baseEnd_8341892 := by
    simpa [prefixWord, tailWord_8341892, baseEnd_8341892] using wordTrace_append hprefix tailTrace_8341892
  have hstable : (prefixWord ++ tailWord_8341892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341892).length < 2 ^ (prefixWord ++ tailWord_8341892).sum := by decide
  have hdescent : baseEnd_8341892 < baseStart_8341892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341902 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_8341902 : Nat := 118140960795 + 8341902 * 2 ^ 59
def prefixEnd_8341902 : Nat := 4983230072969 + 3 ^ 40 * 8341902 * 2
def baseEnd_8341902 : Nat := 1427801766234108834587099

theorem tailTrace_8341902 : CollatzResearch.WordTrace tailWord_8341902 prefixEnd_8341902 1427801766234108834587099 := by
  unfold tailWord_8341902
  simp only [CollatzResearch.WordTrace]
  refine ⟨38031770178090151535233495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202836107616480808187911973 38031770178090151535233495)
  ·
    refine ⟨57047655267135227302850243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38031770178090151535233495 57047655267135227302850243)
    ·
      refine ⟨85571482900702840954275365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57047655267135227302850243 85571482900702840954275365)
      ·
        refine ⟨16044653043881782678926631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85571482900702840954275365 16044653043881782678926631)
        ·
          refine ⟨24066979565822674018389947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16044653043881782678926631 24066979565822674018389947)
          ·
            refine ⟨36100469348734011027584921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24066979565822674018389947 36100469348734011027584921)
            ·
              refine ⟨27075352011550508270688691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36100469348734011027584921 27075352011550508270688691)
              ·
                refine ⟨40613028017325762406033037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27075352011550508270688691 40613028017325762406033037)
                ·
                  refine ⟨15229885506497160902262389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40613028017325762406033037 15229885506497160902262389)
                  ·
                    refine ⟨1427801766234108834587099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15229885506497160902262389 1427801766234108834587099)
                    ·
                      rfl

theorem cell23_8341902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_8341902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341902 prefixEnd_8341902 := by exact prefixLift 8341902
  have htrace : WordTrace (prefixWord ++ tailWord_8341902) baseStart_8341902 baseEnd_8341902 := by
    simpa [prefixWord, tailWord_8341902, baseEnd_8341902] using wordTrace_append hprefix tailTrace_8341902
  have hstable : (prefixWord ++ tailWord_8341902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341902).length < 2 ^ (prefixWord ++ tailWord_8341902).sum := by decide
  have hdescent : baseEnd_8341902 < baseStart_8341902 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341925 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_8341925 : Nat := 118140960795 + 8341925 * 2 ^ 59
def prefixEnd_8341925 : Nat := 4983230072969 + 3 ^ 40 * 8341925 * 2
def baseEnd_8341925 : Nat := 4283417108757379913773691

theorem tailTrace_8341925 : CollatzResearch.WordTrace tailWord_8341925 prefixEnd_8341925 4283417108757379913773691 := by
  unfold tailWord_8341925
  simp only [CollatzResearch.WordTrace]
  refine ⟨304255000303637887209955229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202836666869091924806636819 304255000303637887209955229)
  ·
    refine ⟨114095625113864207703733211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304255000303637887209955229 114095625113864207703733211)
    ·
      refine ⟨171143437670796311555599817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114095625113864207703733211 171143437670796311555599817)
      ·
        refine ⟨128357578253097233666699863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171143437670796311555599817 128357578253097233666699863)
        ·
          refine ⟨192536367379645850500049795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128357578253097233666699863 192536367379645850500049795)
          ·
            refine ⟨288804551069468775750074693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192536367379645850500049795 288804551069468775750074693)
            ·
              refine ⟨54150853325525395453139005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288804551069468775750074693 54150853325525395453139005)
              ·
                refine ⟨20306569997072023294927127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54150853325525395453139005 20306569997072023294927127)
                ·
                  refine ⟨30459854995608034942390691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20306569997072023294927127 30459854995608034942390691)
                  ·
                    refine ⟨45689782493412052413586037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30459854995608034942390691 45689782493412052413586037)
                    ·
                      refine ⟨4283417108757379913773691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45689782493412052413586037 4283417108757379913773691)
                      ·
                        rfl

theorem cell23_8341925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_8341925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341925 prefixEnd_8341925 := by exact prefixLift 8341925
  have htrace : WordTrace (prefixWord ++ tailWord_8341925) baseStart_8341925 baseEnd_8341925 := by
    simpa [prefixWord, tailWord_8341925, baseEnd_8341925] using wordTrace_append hprefix tailTrace_8341925
  have hstable : (prefixWord ++ tailWord_8341925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341925).length < 2 ^ (prefixWord ++ tailWord_8341925).sum := by decide
  have hdescent : baseEnd_8341925 < baseStart_8341925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341953 : List Nat := [1, 2, 7, 1, 1, 1, 2, 2, 1, 5]
def baseStart_8341953 : Nat := 118140960795 + 8341953 * 2 ^ 59
def prefixEnd_8341953 : Nat := 4983230072969 + 3 ^ 40 * 8341953 * 2
def baseEnd_8341953 : Nat := 1427810495405235268074521

theorem tailTrace_8341953 : CollatzResearch.WordTrace tailWord_8341953 prefixEnd_8341953 1427810495405235268074521 := by
  unfold tailWord_8341953
  simp only [CollatzResearch.WordTrace]
  refine ⟨304256021547536447991974513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202837347698357631994649675 304256021547536447991974513)
  ·
    refine ⟨228192016160652335993980885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304256021547536447991974513 228192016160652335993980885)
    ·
      refine ⟨5348250378765289124858927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 228192016160652335993980885 5348250378765289124858927)
      ·
        refine ⟨8022375568147933687288391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5348250378765289124858927 8022375568147933687288391)
        ·
          refine ⟨12033563352221900530932587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8022375568147933687288391 12033563352221900530932587)
          ·
            refine ⟨18050345028332850796398881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12033563352221900530932587 18050345028332850796398881)
            ·
              refine ⟨13537758771249638097299161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18050345028332850796398881 13537758771249638097299161)
              ·
                refine ⟨10153319078437228572974371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13537758771249638097299161 10153319078437228572974371)
                ·
                  refine ⟨15229978617655842859461557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10153319078437228572974371 15229978617655842859461557)
                  ·
                    refine ⟨1427810495405235268074521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15229978617655842859461557 1427810495405235268074521)
                    ·
                      rfl

theorem cell23_8341953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_8341953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341953 prefixEnd_8341953 := by exact prefixLift 8341953
  have htrace : WordTrace (prefixWord ++ tailWord_8341953) baseStart_8341953 baseEnd_8341953 := by
    simpa [prefixWord, tailWord_8341953, baseEnd_8341953] using wordTrace_append hprefix tailTrace_8341953
  have hstable : (prefixWord ++ tailWord_8341953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341953).length < 2 ^ (prefixWord ++ tailWord_8341953).sum := by decide
  have hdescent : baseEnd_8341953 < baseStart_8341953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341956 : List Nat := [2, 3, 3, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_8341956 : Nat := 118140960795 + 8341956 * 2 ^ 59
def prefixEnd_8341956 : Nat := 4983230072969 + 3 ^ 40 * 8341956 * 2
def baseEnd_8341956 : Nat := 4283433026657669292486049

theorem tailTrace_8341956 : CollatzResearch.WordTrace tailWord_8341956 prefixEnd_8341956 4283433026657669292486049 := by
  unfold tailWord_8341956
  simp only [CollatzResearch.WordTrace]
  refine ⟨152128065483262789752166861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202837420644350386336222481 152128065483262789752166861)
  ·
    refine ⟨57048024556223546157062573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152128065483262789752166861 57048024556223546157062573)
    ·
      refine ⟨21393009208583829808898465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57048024556223546157062573 21393009208583829808898465)
      ·
        refine ⟨16044756906437872356673849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21393009208583829808898465 16044756906437872356673849)
        ·
          refine ⟨12033567679828404267505387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16044756906437872356673849 12033567679828404267505387)
          ·
            refine ⟨18050351519742606401258081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12033567679828404267505387 18050351519742606401258081)
            ·
              refine ⟨13537763639806954800943561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18050351519742606401258081 13537763639806954800943561)
              ·
                refine ⟨10153322729855216100707671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13537763639806954800943561 10153322729855216100707671)
                ·
                  refine ⟨15229984094782824151061507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10153322729855216100707671 15229984094782824151061507)
                  ·
                    refine ⟨22844976142174236226592261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15229984094782824151061507 22844976142174236226592261)
                    ·
                      refine ⟨4283433026657669292486049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22844976142174236226592261 4283433026657669292486049)
                      ·
                        rfl

theorem cell23_8341956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_8341956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341956 prefixEnd_8341956 := by exact prefixLift 8341956
  have htrace : WordTrace (prefixWord ++ tailWord_8341956) baseStart_8341956 baseEnd_8341956 := by
    simpa [prefixWord, tailWord_8341956, baseEnd_8341956] using wordTrace_append hprefix tailTrace_8341956
  have hstable : (prefixWord ++ tailWord_8341956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341956).length < 2 ^ (prefixWord ++ tailWord_8341956).sum := by decide
  have hdescent : baseEnd_8341956 < baseStart_8341956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341959 : List Nat := [1, 1, 4, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_8341959 : Nat := 118140960795 + 8341959 * 2 ^ 59
def prefixEnd_8341959 : Nat := 4983230072969 + 3 ^ 40 * 8341959 * 2
def baseEnd_8341959 : Nat := 4283434567099632780748535

theorem tailTrace_8341959 : CollatzResearch.WordTrace tailWord_8341959 prefixEnd_8341959 4283434567099632780748535 := by
  unfold tailWord_8341959
  simp only [CollatzResearch.WordTrace]
  refine ⟨304256240385514711016692931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202837493590343140677795287 304256240385514711016692931)
  ·
    refine ⟨456384360578272066525039397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304256240385514711016692931 456384360578272066525039397)
    ·
      refine ⟨85572067608426012473444887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456384360578272066525039397 85572067608426012473444887)
      ·
        refine ⟨128358101412639018710167331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85572067608426012473444887 128358101412639018710167331)
        ·
          refine ⟨192537152118958528065250997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128358101412639018710167331 192537152118958528065250997)
          ·
            refine ⟨18050358011152362006117281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192537152118958528065250997 18050358011152362006117281)
            ·
              refine ⟨13537768508364271504587961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18050358011152362006117281 13537768508364271504587961)
              ·
                refine ⟨10153326381273203628440971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13537768508364271504587961 10153326381273203628440971)
                ·
                  refine ⟨15229989571909805442661457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10153326381273203628440971 15229989571909805442661457)
                  ·
                    refine ⟨11422492178932354081996093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15229989571909805442661457 11422492178932354081996093)
                    ·
                      refine ⟨4283434567099632780748535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11422492178932354081996093 4283434567099632780748535)
                      ·
                        rfl

theorem cell23_8341959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_8341959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341959 prefixEnd_8341959 := by exact prefixLift 8341959
  have htrace : WordTrace (prefixWord ++ tailWord_8341959) baseStart_8341959 baseEnd_8341959 := by
    simpa [prefixWord, tailWord_8341959, baseEnd_8341959] using wordTrace_append hprefix tailTrace_8341959
  have hstable : (prefixWord ++ tailWord_8341959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341959).length < 2 ^ (prefixWord ++ tailWord_8341959).sum := by decide
  have hdescent : baseEnd_8341959 < baseStart_8341959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341973 : List Nat := [1, 3, 2, 3, 1, 2, 3, 3, 1, 2, 2]
def baseStart_8341973 : Nat := 118140960795 + 8341973 * 2 ^ 59
def prefixEnd_8341973 : Nat := 4983230072969 + 3 ^ 40 * 8341973 * 2
def baseEnd_8341973 : Nat := 4283441755828795725973471

theorem tailTrace_8341973 : CollatzResearch.WordTrace tailWord_8341973 prefixEnd_8341973 4283441755828795725973471 := by
  unfold tailWord_8341973
  simp only [CollatzResearch.WordTrace]
  refine ⟨304256751007463991407702573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202837834004975994271801715 304256751007463991407702573)
  ·
    refine ⟨114096281627798996777888465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304256751007463991407702573 114096281627798996777888465)
    ·
      refine ⟨85572211220849247583416349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114096281627798996777888465 85572211220849247583416349)
      ·
        refine ⟨32089579207818467843781131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85572211220849247583416349 32089579207818467843781131)
        ·
          refine ⟨48134368811727701765671697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32089579207818467843781131 48134368811727701765671697)
          ·
            refine ⟨36100776608795776324253773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48134368811727701765671697 36100776608795776324253773)
            ·
              refine ⟨13537791228298416121595165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36100776608795776324253773 13537791228298416121595165)
              ·
                refine ⟨5076671710611906045598187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13537791228298416121595165 5076671710611906045598187)
                ·
                  refine ⟨7615007565917859068397281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076671710611906045598187 7615007565917859068397281)
                  ·
                    refine ⟨5711255674438394301297961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7615007565917859068397281 5711255674438394301297961)
                    ·
                      refine ⟨4283441755828795725973471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711255674438394301297961 4283441755828795725973471)
                      ·
                        rfl

theorem cell23_8341973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_8341973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341973 prefixEnd_8341973 := by exact prefixLift 8341973
  have htrace : WordTrace (prefixWord ++ tailWord_8341973) baseStart_8341973 baseEnd_8341973 := by
    simpa [prefixWord, tailWord_8341973, baseEnd_8341973] using wordTrace_append hprefix tailTrace_8341973
  have hstable : (prefixWord ++ tailWord_8341973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341973).length < 2 ^ (prefixWord ++ tailWord_8341973).sum := by decide
  have hdescent : baseEnd_8341973 < baseStart_8341973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341985 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_8341985 : Nat := 118140960795 + 8341985 * 2 ^ 59
def prefixEnd_8341985 : Nat := 4983230072969 + 3 ^ 40 * 8341985 * 2
def baseEnd_8341985 : Nat := 4283447917596649679023415

theorem tailTrace_8341985 : CollatzResearch.WordTrace tailWord_8341985 prefixEnd_8341985 4283447917596649679023415 := by
  unfold tailWord_8341985
  simp only [CollatzResearch.WordTrace]
  refine ⟨304257188683420517457139409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202838125788947011638092939 304257188683420517457139409)
  ·
    refine ⟨228192891512565388092854557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304257188683420517457139409 228192891512565388092854557)
    ·
      refine ⟨85572334317212020534820459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228192891512565388092854557 85572334317212020534820459)
      ·
        refine ⟨128358501475818030802230689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85572334317212020534820459 128358501475818030802230689)
        ·
          refine ⟨96268876106863523101673017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128358501475818030802230689 96268876106863523101673017)
          ·
            refine ⟨72201657080147642326254763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96268876106863523101673017 72201657080147642326254763)
            ·
              refine ⟨108302485620221463489382145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72201657080147642326254763 108302485620221463489382145)
              ·
                refine ⟨81226864215166097617036609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108302485620221463489382145 81226864215166097617036609)
                ·
                  refine ⟨60920148161374573212777457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81226864215166097617036609 60920148161374573212777457)
                  ·
                    refine ⟨45690111121030929909583093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60920148161374573212777457 45690111121030929909583093)
                    ·
                      refine ⟨4283447917596649679023415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45690111121030929909583093 4283447917596649679023415)
                      ·
                        rfl

theorem cell23_8341985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_8341985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341985 prefixEnd_8341985 := by exact prefixLift 8341985
  have htrace : WordTrace (prefixWord ++ tailWord_8341985) baseStart_8341985 baseEnd_8341985 := by
    simpa [prefixWord, tailWord_8341985, baseEnd_8341985] using wordTrace_append hprefix tailTrace_8341985
  have hstable : (prefixWord ++ tailWord_8341985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341985).length < 2 ^ (prefixWord ++ tailWord_8341985).sum := by decide
  have hdescent : baseEnd_8341985 < baseStart_8341985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341995 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 4]
def baseStart_8341995 : Nat := 118140960795 + 8341995 * 2 ^ 59
def prefixEnd_8341995 : Nat := 4983230072969 + 3 ^ 40 * 8341995 * 2
def baseEnd_8341995 : Nat := 4283453052403194639898369

theorem tailTrace_8341995 : CollatzResearch.WordTrace tailWord_8341995 prefixEnd_8341995 4283453052403194639898369 := by
  unfold tailWord_8341995
  simp only [CollatzResearch.WordTrace]
  refine ⟨304257553413384289165003439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202838368942256192776668959 304257553413384289165003439)
  ·
    refine ⟨456386330120076433747505159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304257553413384289165003439 456386330120076433747505159)
    ·
      refine ⟨684579495180114650621257739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456386330120076433747505159 684579495180114650621257739)
      ·
        refine ⟨1026869242770171975931886609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684579495180114650621257739 1026869242770171975931886609)
        ·
          refine ⟨770151932077628981948914957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1026869242770171975931886609 770151932077628981948914957)
          ·
            refine ⟨288806974529110868230843109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 770151932077628981948914957 288806974529110868230843109)
            ·
              refine ⟨54151307724208287793283083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288806974529110868230843109 54151307724208287793283083)
              ·
                refine ⟨81226961586312431689924625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54151307724208287793283083 81226961586312431689924625)
                ·
                  refine ⟨60920221189734323767443469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81226961586312431689924625 60920221189734323767443469)
                  ·
                    refine ⟨22845082946150371412791301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60920221189734323767443469 22845082946150371412791301)
                    ·
                      refine ⟨4283453052403194639898369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22845082946150371412791301 4283453052403194639898369)
                      ·
                        rfl

theorem cell23_8341995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 4].length) (baseStart_8341995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8341995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8341995 prefixEnd_8341995 := by exact prefixLift 8341995
  have htrace : WordTrace (prefixWord ++ tailWord_8341995) baseStart_8341995 baseEnd_8341995 := by
    simpa [prefixWord, tailWord_8341995, baseEnd_8341995] using wordTrace_append hprefix tailTrace_8341995
  have hstable : (prefixWord ++ tailWord_8341995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341995).length < 2 ^ (prefixWord ++ tailWord_8341995).sum := by decide
  have hdescent : baseEnd_8341995 < baseStart_8341995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342006 : List Nat := [5, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_8342006 : Nat := 118140960795 + 8342006 * 2 ^ 59
def prefixEnd_8342006 : Nat := 4983230072969 + 3 ^ 40 * 8342006 * 2
def baseEnd_8342006 : Nat := 4283458700690394096860819

theorem tailTrace_8342006 : CollatzResearch.WordTrace tailWord_8342006 prefixEnd_8342006 4283458700690394096860819 := by
  unfold tailWord_8342006
  simp only [CollatzResearch.WordTrace]
  refine ⟨19016122163521527377728367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202838636410896292029102581 19016122163521527377728367)
  ·
    refine ⟨28524183245282291066592551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19016122163521527377728367 28524183245282291066592551)
    ·
      refine ⟨42786274867923436599888827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28524183245282291066592551 42786274867923436599888827)
      ·
        refine ⟨64179412301885154899833241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42786274867923436599888827 64179412301885154899833241)
        ·
          refine ⟨48134559226413866174874931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64179412301885154899833241 48134559226413866174874931)
          ·
            refine ⟨72201838839620799262312397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48134559226413866174874931 72201838839620799262312397)
            ·
              refine ⟨27075689564857799723367149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72201838839620799262312397 27075689564857799723367149)
              ·
                refine ⟨10153383586821674896262681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27075689564857799723367149 10153383586821674896262681)
                ·
                  refine ⟨7615037690116256172197011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10153383586821674896262681 7615037690116256172197011)
                  ·
                    refine ⟨11422556535174384258295517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7615037690116256172197011 11422556535174384258295517)
                    ·
                      refine ⟨4283458700690394096860819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11422556535174384258295517 4283458700690394096860819)
                      ·
                        rfl

theorem cell23_8342006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_8342006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342006 prefixEnd_8342006 := by exact prefixLift 8342006
  have htrace : WordTrace (prefixWord ++ tailWord_8342006) baseStart_8342006 baseEnd_8342006 := by
    simpa [prefixWord, tailWord_8342006, baseEnd_8342006] using wordTrace_append hprefix tailTrace_8342006
  have hstable : (prefixWord ++ tailWord_8342006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342006).length < 2 ^ (prefixWord ++ tailWord_8342006).sum := by decide
  have hdescent : baseEnd_8342006 < baseStart_8342006 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342015 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 5]
def baseStart_8342015 : Nat := 118140960795 + 8342015 * 2 ^ 59
def prefixEnd_8342015 : Nat := 4983230072969 + 3 ^ 40 * 8342015 * 2
def baseEnd_8342015 : Nat := 4283463322016284561648277

theorem tailTrace_8342015 : CollatzResearch.WordTrace tailWord_8342015 prefixEnd_8342015 4283463322016284561648277 := by
  unfold tailWord_8342015
  simp only [CollatzResearch.WordTrace]
  refine ⟨304258282873311832580731499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202838855248874555053820999 304258282873311832580731499)
  ·
    refine ⟨456387424309967748871097249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304258282873311832580731499 456387424309967748871097249)
    ·
      refine ⟨342290568232475811653322937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456387424309967748871097249 342290568232475811653322937)
      ·
        refine ⟨256717926174356858739992203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342290568232475811653322937 256717926174356858739992203)
        ·
          refine ⟨385076889261535288109988305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256717926174356858739992203 385076889261535288109988305)
          ·
            refine ⟨288807666946151466082491229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385076889261535288109988305 288807666946151466082491229)
            ·
              refine ⟨108302875104806799780934211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288807666946151466082491229 108302875104806799780934211)
              ·
                refine ⟨162454312657210199671401317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108302875104806799780934211 162454312657210199671401317)
                ·
                  refine ⟨30460183623226912438387747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162454312657210199671401317 30460183623226912438387747)
                  ·
                    refine ⟨45690275434840368657581621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30460183623226912438387747 45690275434840368657581621)
                    ·
                      refine ⟨4283463322016284561648277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45690275434840368657581621 4283463322016284561648277)
                      ·
                        rfl

theorem cell23_8342015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_8342015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342015 prefixEnd_8342015 := by exact prefixLift 8342015
  have htrace : WordTrace (prefixWord ++ tailWord_8342015) baseStart_8342015 baseEnd_8342015 := by
    simpa [prefixWord, tailWord_8342015, baseEnd_8342015] using wordTrace_append hprefix tailTrace_8342015
  have hstable : (prefixWord ++ tailWord_8342015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342015).length < 2 ^ (prefixWord ++ tailWord_8342015).sum := by decide
  have hdescent : baseEnd_8342015 < baseStart_8342015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342025 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 3, 4, 4]
def baseStart_8342025 : Nat := 118140960795 + 8342025 * 2 ^ 59
def prefixEnd_8342025 : Nat := 4983230072969 + 3 ^ 40 * 8342025 * 2
def baseEnd_8342025 : Nat := 4283468456822829522523231

theorem tailTrace_8342025 : CollatzResearch.WordTrace tailWord_8342025 prefixEnd_8342025 4283468456822829522523231 := by
  unfold tailWord_8342025
  simp only [CollatzResearch.WordTrace]
  refine ⟨304258647603275604288595529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202839098402183736192397019 304258647603275604288595529)
  ·
    refine ⟨228193985702456703216446647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304258647603275604288595529 228193985702456703216446647)
    ·
      refine ⟨342290978553685054824669971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228193985702456703216446647 342290978553685054824669971)
      ·
        refine ⟨513436467830527582237004957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342290978553685054824669971 513436467830527582237004957)
        ·
          refine ⟨192538675436447843338876859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513436467830527582237004957 192538675436447843338876859)
          ·
            refine ⟨288808013154671765008315289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192538675436447843338876859 288808013154671765008315289)
            ·
              refine ⟨216606009866003823756236467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288808013154671765008315289 216606009866003823756236467)
              ·
                refine ⟨324909014799005735634354701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216606009866003823756236467 324909014799005735634354701)
                ·
                  refine ⟨121840880549627150862883013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324909014799005735634354701 121840880549627150862883013)
                  ·
                    refine ⟨22845165103055090786790565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121840880549627150862883013 22845165103055090786790565)
                    ·
                      refine ⟨4283468456822829522523231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22845165103055090786790565 4283468456822829522523231)
                      ·
                        rfl

theorem cell23_8342025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_8342025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342025 prefixEnd_8342025 := by exact prefixLift 8342025
  have htrace : WordTrace (prefixWord ++ tailWord_8342025) baseStart_8342025 baseEnd_8342025 := by
    simpa [prefixWord, tailWord_8342025, baseEnd_8342025] using wordTrace_append hprefix tailTrace_8342025
  have hstable : (prefixWord ++ tailWord_8342025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342025).length < 2 ^ (prefixWord ++ tailWord_8342025).sum := by decide
  have hdescent : baseEnd_8342025 < baseStart_8342025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342084 : List Nat := [2, 3, 5, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_8342084 : Nat := 118140960795 + 8342084 * 2 ^ 59
def prefixEnd_8342084 : Nat := 4983230072969 + 3 ^ 40 * 8342084 * 2
def baseEnd_8342084 : Nat := 4283498752181444791685461

theorem tailTrace_8342084 : CollatzResearch.WordTrace tailWord_8342084 prefixEnd_8342084 4283498752181444791685461 := by
  unfold tailWord_8342084
  simp only [CollatzResearch.WordTrace]
  refine ⟨152130399755030928682496653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202840533006707904909995537 152130399755030928682496653)
  ·
    refine ⟨57048899908136598255936245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152130399755030928682496653 57048899908136598255936245)
    ·
      refine ⟨5348334366387806086494023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57048899908136598255936245 5348334366387806086494023)
      ·
        refine ⟨8022501549581709129741035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5348334366387806086494023 8022501549581709129741035)
        ·
          refine ⟨12033752324372563694611553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8022501549581709129741035 12033752324372563694611553)
          ·
            refine ⟨9025314243279422770958665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12033752324372563694611553 9025314243279422770958665)
            ·
              refine ⟨6768985682459567078218999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9025314243279422770958665 6768985682459567078218999)
              ·
                refine ⟨10153478523689350617328499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768985682459567078218999 10153478523689350617328499)
                ·
                  refine ⟨15230217785534025925992749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10153478523689350617328499 15230217785534025925992749)
                  ·
                    refine ⟨5711331669575259722247281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15230217785534025925992749 5711331669575259722247281)
                    ·
                      refine ⟨4283498752181444791685461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711331669575259722247281 4283498752181444791685461)
                      ·
                        rfl

theorem cell23_8342084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_8342084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342084 prefixEnd_8342084 := by exact prefixLift 8342084
  have htrace : WordTrace (prefixWord ++ tailWord_8342084) baseStart_8342084 baseEnd_8342084 := by
    simpa [prefixWord, tailWord_8342084, baseEnd_8342084] using wordTrace_append hprefix tailTrace_8342084
  have hstable : (prefixWord ++ tailWord_8342084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342084).length < 2 ^ (prefixWord ++ tailWord_8342084).sum := by decide
  have hdescent : baseEnd_8342084 < baseStart_8342084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342179 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 1, 5, 2]
def baseStart_8342179 : Nat := 118140960795 + 8342179 * 2 ^ 59
def prefixEnd_8342179 : Nat := 4983230072969 + 3 ^ 40 * 8342179 * 2
def baseEnd_8342179 : Nat := 4283547532843621919997523

theorem tailTrace_8342179 : CollatzResearch.WordTrace tailWord_8342179 prefixEnd_8342179 4283547532843621919997523 := by
  unfold tailWord_8342179
  simp only [CollatzResearch.WordTrace]
  refine ⟨304264264444717688589701591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202842842963145125726467727 304264264444717688589701591)
  ·
    refine ⟨456396396667076532884552387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304264264444717688589701591 456396396667076532884552387)
    ·
      refine ⟨684594595000614799326828581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456396396667076532884552387 684594595000614799326828581)
      ·
        refine ⟨128361486562615274873780359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 684594595000614799326828581 128361486562615274873780359)
        ·
          refine ⟨192542229843922912310670539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128361486562615274873780359 192542229843922912310670539)
          ·
            refine ⟨288813344765884368466005809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192542229843922912310670539 288813344765884368466005809)
            ·
              refine ⟨216610008574413276349504357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288813344765884368466005809 216610008574413276349504357)
              ·
                refine ⟨40614376607702489315532067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216610008574413276349504357 40614376607702489315532067)
                ·
                  refine ⟨60921564911553733973298101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40614376607702489315532067 60921564911553733973298101)
                  ·
                    refine ⟨5711396710458162559996697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60921564911553733973298101 5711396710458162559996697)
                    ·
                      refine ⟨4283547532843621919997523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711396710458162559996697 4283547532843621919997523)
                      ·
                        rfl

theorem cell23_8342179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_8342179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342179 prefixEnd_8342179 := by exact prefixLift 8342179
  have htrace : WordTrace (prefixWord ++ tailWord_8342179) baseStart_8342179 baseEnd_8342179 := by
    simpa [prefixWord, tailWord_8342179, baseEnd_8342179] using wordTrace_append hprefix tailTrace_8342179
  have hstable : (prefixWord ++ tailWord_8342179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342179).length < 2 ^ (prefixWord ++ tailWord_8342179).sum := by decide
  have hdescent : baseEnd_8342179 < baseStart_8342179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342220 : List Nat := [2, 2, 1, 5, 1, 2, 1, 4, 1, 1, 3]
def baseStart_8342220 : Nat := 118140960795 + 8342220 * 2 ^ 59
def prefixEnd_8342220 : Nat := 4983230072969 + 3 ^ 40 * 8342220 * 2
def baseEnd_8342220 : Nat := 4283568585550456259584835

theorem tailTrace_8342220 : CollatzResearch.WordTrace tailWord_8342220 prefixEnd_8342220 4283568585550456259584835 := by
  unfold tailWord_8342220
  simp only [CollatzResearch.WordTrace]
  refine ⟨152132879918784576295972057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202843839891712768394629409 152132879918784576295972057)
  ·
    refine ⟨114099659939088432221979043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152132879918784576295972057 114099659939088432221979043)
    ·
      refine ⟨171149489908632648332968565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114099659939088432221979043 171149489908632648332968565)
      ·
        refine ⟨16045264678934310781215803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171149489908632648332968565 16045264678934310781215803)
        ·
          refine ⟨24067897018401466171823705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16045264678934310781215803 24067897018401466171823705)
          ·
            refine ⟨18050922763801099628867779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24067897018401466171823705 18050922763801099628867779)
            ·
              refine ⟨27076384145701649443301669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18050922763801099628867779 27076384145701649443301669)
              ·
                refine ⟨5076822027319059270619063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27076384145701649443301669 5076822027319059270619063)
                ·
                  refine ⟨7615233040978588905928595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076822027319059270619063 7615233040978588905928595)
                  ·
                    refine ⟨11422849561467883358892893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7615233040978588905928595 11422849561467883358892893)
                    ·
                      refine ⟨4283568585550456259584835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11422849561467883358892893 4283568585550456259584835)
                      ·
                        rfl

theorem cell23_8342220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_8342220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342220 prefixEnd_8342220 := by exact prefixLift 8342220
  have htrace : WordTrace (prefixWord ++ tailWord_8342220) baseStart_8342220 baseEnd_8342220 := by
    simpa [prefixWord, tailWord_8342220, baseEnd_8342220] using wordTrace_append hprefix tailTrace_8342220
  have hstable : (prefixWord ++ tailWord_8342220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342220).length < 2 ^ (prefixWord ++ tailWord_8342220).sum := by decide
  have hdescent : baseEnd_8342220 < baseStart_8342220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342236 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 1, 6]
def baseStart_8342236 : Nat := 118140960795 + 8342236 * 2 ^ 59
def prefixEnd_8342236 : Nat := 4983230072969 + 3 ^ 40 * 8342236 * 2
def baseEnd_8342236 : Nat := 1427858933746976065661587

theorem tailTrace_8342236 : CollatzResearch.WordTrace tailWord_8342236 prefixEnd_8342236 1427858933746976065661587 := by
  unfold tailWord_8342236
  simp only [CollatzResearch.WordTrace]
  refine ⟨152133171702755593662263281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202844228937007458216351041 152133171702755593662263281)
  ·
    refine ⟨114099878777066695246697461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152133171702755593662263281 114099878777066695246697461)
    ·
      refine ⟨10696863635350002679377887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114099878777066695246697461 10696863635350002679377887)
      ·
        refine ⟨16045295453025004019066831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10696863635350002679377887 16045295453025004019066831)
        ·
          refine ⟨24067943179537506028600247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16045295453025004019066831 24067943179537506028600247)
          ·
            refine ⟨36101914769306259042900371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24067943179537506028600247 36101914769306259042900371)
            ·
              refine ⟨54152872153959388564350557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36101914769306259042900371 54152872153959388564350557)
              ·
                refine ⟨20307327057734770711631459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54152872153959388564350557 20307327057734770711631459)
                ·
                  refine ⟨30460990586602156067447189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20307327057734770711631459 30460990586602156067447189)
                  ·
                    refine ⟨1427858933746976065661587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30460990586602156067447189 1427858933746976065661587)
                    ·
                      rfl

theorem cell23_8342236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_8342236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342236 prefixEnd_8342236 := by exact prefixLift 8342236
  have htrace : WordTrace (prefixWord ++ tailWord_8342236) baseStart_8342236 baseEnd_8342236 := by
    simpa [prefixWord, tailWord_8342236, baseEnd_8342236] using wordTrace_append hprefix tailTrace_8342236
  have hstable : (prefixWord ++ tailWord_8342236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342236).length < 2 ^ (prefixWord ++ tailWord_8342236).sum := by decide
  have hdescent : baseEnd_8342236 < baseStart_8342236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342239 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 4]
def baseStart_8342239 : Nat := 118140960795 + 8342239 * 2 ^ 59
def prefixEnd_8342239 : Nat := 4983230072969 + 3 ^ 40 * 8342239 * 2
def baseEnd_8342239 : Nat := 4283578341682891685247247

theorem tailTrace_8342239 : CollatzResearch.WordTrace tailWord_8342239 prefixEnd_8342239 4283578341682891685247247 := by
  unfold tailWord_8342239
  simp only [CollatzResearch.WordTrace]
  refine ⟨304266452824500318836885771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202844301883000212557923847 304266452824500318836885771)
  ·
    refine ⟨456399679236750478255328657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304266452824500318836885771 456399679236750478255328657)
    ·
      refine ⟨342299759427562858691496493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456399679236750478255328657 342299759427562858691496493)
      ·
        refine ⟨128362409785336072009311185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342299759427562858691496493 128362409785336072009311185)
        ·
          refine ⟨96271807339002054006983389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128362409785336072009311185 96271807339002054006983389)
          ·
            refine ⟨36101927752125770252618771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96271807339002054006983389 36101927752125770252618771)
            ·
              refine ⟨54152891628188655378928157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36101927752125770252618771 54152891628188655378928157)
              ·
                refine ⟨20307334360570745767098059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54152891628188655378928157 20307334360570745767098059)
                ·
                  refine ⟨30461001540856118650647089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20307334360570745767098059 30461001540856118650647089)
                  ·
                    refine ⟨22845751155642088987985317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30461001540856118650647089 22845751155642088987985317)
                    ·
                      refine ⟨4283578341682891685247247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22845751155642088987985317 4283578341682891685247247)
                      ·
                        rfl

theorem cell23_8342239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_8342239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342239 prefixEnd_8342239 := by exact prefixLift 8342239
  have htrace : WordTrace (prefixWord ++ tailWord_8342239) baseStart_8342239 baseEnd_8342239 := by
    simpa [prefixWord, tailWord_8342239, baseEnd_8342239] using wordTrace_append hprefix tailTrace_8342239
  have hstable : (prefixWord ++ tailWord_8342239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342239).length < 2 ^ (prefixWord ++ tailWord_8342239).sum := by decide
  have hdescent : baseEnd_8342239 < baseStart_8342239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342243 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 5, 2, 2]
def baseStart_8342243 : Nat := 118140960795 + 8342243 * 2 ^ 59
def prefixEnd_8342243 : Nat := 4983230072969 + 3 ^ 40 * 8342243 * 2
def baseEnd_8342243 : Nat := 4283580395605509669597229

theorem tailTrace_8342243 : CollatzResearch.WordTrace tailWord_8342243 prefixEnd_8342243 4283580395605509669597229 := by
  unfold tailWord_8342243
  simp only [CollatzResearch.WordTrace]
  refine ⟨304266598716485827520031383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202844399144323885013354255 304266598716485827520031383)
  ·
    refine ⟨456399898074728741280047075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304266598716485827520031383 456399898074728741280047075)
    ·
      refine ⟨684599847112093111920070613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456399898074728741280047075 684599847112093111920070613)
      ·
        refine ⟨16045308916689682310626655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 684599847112093111920070613 16045308916689682310626655)
        ·
          refine ⟨24067963375034523465939983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16045308916689682310626655 24067963375034523465939983)
          ·
            refine ⟨36101945062551785198909975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24067963375034523465939983 36101945062551785198909975)
            ·
              refine ⟨54152917593827677798364963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36101945062551785198909975 54152917593827677798364963)
              ·
                refine ⟨81229376390741516697547445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54152917593827677798364963 81229376390741516697547445)
                ·
                  refine ⟨7615254036632017190395073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81229376390741516697547445 7615254036632017190395073)
                  ·
                    refine ⟨5711440527474012892796305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7615254036632017190395073 5711440527474012892796305)
                    ·
                      refine ⟨4283580395605509669597229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711440527474012892796305 4283580395605509669597229)
                      ·
                        rfl

theorem cell23_8342243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_8342243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342243 prefixEnd_8342243 := by exact prefixLift 8342243
  have htrace : WordTrace (prefixWord ++ tailWord_8342243) baseStart_8342243 baseEnd_8342243 := by
    simpa [prefixWord, tailWord_8342243, baseEnd_8342243] using wordTrace_append hprefix tailTrace_8342243
  have hstable : (prefixWord ++ tailWord_8342243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342243).length < 2 ^ (prefixWord ++ tailWord_8342243).sum := by decide
  have hdescent : baseEnd_8342243 < baseStart_8342243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342270 : List Nat := [4, 2, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_8342270 : Nat := 118140960795 + 8342270 * 2 ^ 59
def prefixEnd_8342270 : Nat := 4983230072969 + 3 ^ 40 * 8342270 * 2
def baseEnd_8342270 : Nat := 1427864753194393687986535

theorem tailTrace_8342270 : CollatzResearch.WordTrace tailWord_8342270 prefixEnd_8342270 1427864753194393687986535 := by
  unfold tailWord_8342270
  simp only [CollatzResearch.WordTrace]
  refine ⟨38033447935923501391408033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202845055658258674087509509 38033447935923501391408033)
  ·
    refine ⟨28525085951942626043556025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38033447935923501391408033 28525085951942626043556025)
    ·
      refine ⟨21393814463956969532667019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28525085951942626043556025 21393814463956969532667019)
      ·
        refine ⟨32090721695935454299000529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21393814463956969532667019 32090721695935454299000529)
        ·
          refine ⟨24068041271951590724250397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32090721695935454299000529 24068041271951590724250397)
          ·
            refine ⟨9025515476981846521593899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24068041271951590724250397 9025515476981846521593899)
            ·
              refine ⟨13538273215472769782390849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9025515476981846521593899 13538273215472769782390849)
              ·
                refine ⟨10153704911604577336793137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13538273215472769782390849 10153704911604577336793137)
                ·
                  refine ⟨7615278683703433002594853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10153704911604577336793137 7615278683703433002594853)
                  ·
                    refine ⟨1427864753194393687986535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7615278683703433002594853 1427864753194393687986535)
                    ·
                      rfl

theorem cell23_8342270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_8342270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342270 prefixEnd_8342270 := by exact prefixLift 8342270
  have htrace : WordTrace (prefixWord ++ tailWord_8342270) baseStart_8342270 baseEnd_8342270 := by
    simpa [prefixWord, tailWord_8342270, baseEnd_8342270] using wordTrace_append hprefix tailTrace_8342270
  have hstable : (prefixWord ++ tailWord_8342270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342270).length < 2 ^ (prefixWord ++ tailWord_8342270).sum := by decide
  have hdescent : baseEnd_8342270 < baseStart_8342270 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342272 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 7]
def baseStart_8342272 : Nat := 118140960795 + 8342272 * 2 ^ 59
def prefixEnd_8342272 : Nat := 4983230072969 + 3 ^ 40 * 8342272 * 2
def baseEnd_8342272 : Nat := 4283595286544490056134595

theorem tailTrace_8342272 : CollatzResearch.WordTrace tailWord_8342272 prefixEnd_8342272 4283595286544490056134595 := by
  unfold tailWord_8342272
  simp only [CollatzResearch.WordTrace]
  refine ⟨152133828216690382736418535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202845104288920510315224713 152133828216690382736418535)
  ·
    refine ⟨228200742325035574104627803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152133828216690382736418535 228200742325035574104627803)
    ·
      refine ⟨342301113487553361156941705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228200742325035574104627803 342301113487553361156941705)
      ·
        refine ⟨256725835115665020867706279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342301113487553361156941705 256725835115665020867706279)
        ·
          refine ⟨385088752673497531301559419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256725835115665020867706279 385088752673497531301559419)
          ·
            refine ⟨577633129010246296952339129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385088752673497531301559419 577633129010246296952339129)
            ·
              refine ⟨433224846757684722714254347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577633129010246296952339129 433224846757684722714254347)
              ·
                refine ⟨649837270136527084071381521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433224846757684722714254347 649837270136527084071381521)
                ·
                  refine ⟨487377952602395313053536141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 649837270136527084071381521 487377952602395313053536141)
                  ·
                    refine ⟨182766732225898242395076053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 487377952602395313053536141 182766732225898242395076053)
                    ·
                      refine ⟨4283595286544490056134595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182766732225898242395076053 4283595286544490056134595)
                      ·
                        rfl

theorem cell23_8342272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_8342272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342272 prefixEnd_8342272 := by exact prefixLift 8342272
  have htrace : WordTrace (prefixWord ++ tailWord_8342272) baseStart_8342272 baseEnd_8342272 := by
    simpa [prefixWord, tailWord_8342272, baseEnd_8342272] using wordTrace_append hprefix tailTrace_8342272
  have hstable : (prefixWord ++ tailWord_8342272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342272).length < 2 ^ (prefixWord ++ tailWord_8342272).sum := by decide
  have hdescent : baseEnd_8342272 < baseStart_8342272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342290 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_8342290 : Nat := 118140960795 + 8342290 * 2 ^ 59
def prefixEnd_8342290 : Nat := 4983230072969 + 3 ^ 40 * 8342290 * 2
def baseEnd_8342290 : Nat := 4283604529196270985709513

theorem tailTrace_8342290 : CollatzResearch.WordTrace tailWord_8342290 prefixEnd_8342290 4283604529196270985709513 := by
  unfold tailWord_8342290
  simp only [CollatzResearch.WordTrace]
  refine ⟨76067078236828888636748081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202845541964877036364661549 76067078236828888636748081)
  ·
    refine ⟨57050308677621666477561061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76067078236828888636748081 57050308677621666477561061)
    ·
      refine ⟨10696932877054062464542699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57050308677621666477561061 10696932877054062464542699)
      ·
        refine ⟨16045399315581093696814049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10696932877054062464542699 16045399315581093696814049)
        ·
          refine ⟨12034049486685820272610537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16045399315581093696814049 12034049486685820272610537)
          ·
            refine ⟨9025537115014365204457903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12034049486685820272610537 9025537115014365204457903)
            ·
              refine ⟨13538305672521547806686855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9025537115014365204457903 13538305672521547806686855)
              ·
                refine ⟨20307458508782321710030283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13538305672521547806686855 20307458508782321710030283)
                ·
                  refine ⟨30461187763173482565045425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20307458508782321710030283 30461187763173482565045425)
                  ·
                    refine ⟨22845890822380111923784069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30461187763173482565045425 22845890822380111923784069)
                    ·
                      refine ⟨4283604529196270985709513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22845890822380111923784069 4283604529196270985709513)
                      ·
                        rfl

theorem cell23_8342290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_8342290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342290 prefixEnd_8342290 := by exact prefixLift 8342290
  have htrace : WordTrace (prefixWord ++ tailWord_8342290) baseStart_8342290 baseEnd_8342290 := by
    simpa [prefixWord, tailWord_8342290, baseEnd_8342290] using wordTrace_append hprefix tailTrace_8342290
  have hstable : (prefixWord ++ tailWord_8342290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342290).length < 2 ^ (prefixWord ++ tailWord_8342290).sum := by decide
  have hdescent : baseEnd_8342290 < baseStart_8342290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342303 : List Nat := [1, 1, 2, 4, 2, 2, 1, 4, 1, 3, 2]
def baseStart_8342303 : Nat := 118140960795 + 8342303 * 2 ^ 59
def prefixEnd_8342303 : Nat := 4983230072969 + 3 ^ 40 * 8342303 * 2
def baseEnd_8342303 : Nat := 4283611204444779434846953

theorem tailTrace_8342303 : CollatzResearch.WordTrace tailWord_8342303 prefixEnd_8342303 4283611204444779434846953 := by
  unfold tailWord_8342303
  simp only [CollatzResearch.WordTrace]
  refine ⟨304268787096268457767215563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202845858064178971844810375 304268787096268457767215563)
  ·
    refine ⟨456403180644402686650823345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304268787096268457767215563 456403180644402686650823345)
    ·
      refine ⟨342302385483302014988117509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456403180644402686650823345 342302385483302014988117509)
      ·
        refine ⟨64181697278119127810272033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342302385483302014988117509 64181697278119127810272033)
        ·
          refine ⟨48136272958589345857704025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64181697278119127810272033 48136272958589345857704025)
          ·
            refine ⟨36102204718942009393278019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48136272958589345857704025 36102204718942009393278019)
            ·
              refine ⟨54153307078413014089917029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36102204718942009393278019 54153307078413014089917029)
              ·
                refine ⟨10153745077202440141859443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54153307078413014089917029 10153745077202440141859443)
                ·
                  refine ⟨15230617615803660212789165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10153745077202440141859443 15230617615803660212789165)
                  ·
                    refine ⟨5711481605926372579795937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15230617615803660212789165 5711481605926372579795937)
                    ·
                      refine ⟨4283611204444779434846953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711481605926372579795937 4283611204444779434846953)
                      ·
                        rfl

theorem cell23_8342303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_8342303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342303 prefixEnd_8342303 := by exact prefixLift 8342303
  have htrace : WordTrace (prefixWord ++ tailWord_8342303) baseStart_8342303 baseEnd_8342303 := by
    simpa [prefixWord, tailWord_8342303, baseEnd_8342303] using wordTrace_append hprefix tailTrace_8342303
  have hstable : (prefixWord ++ tailWord_8342303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342303).length < 2 ^ (prefixWord ++ tailWord_8342303).sum := by decide
  have hdescent : baseEnd_8342303 < baseStart_8342303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342316 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 3, 4, 2]
def baseStart_8342316 : Nat := 118140960795 + 8342316 * 2 ^ 59
def prefixEnd_8342316 : Nat := 4983230072969 + 3 ^ 40 * 8342316 * 2
def baseEnd_8342316 : Nat := 4283617879693287883984393

theorem tailTrace_8342316 : CollatzResearch.WordTrace tailWord_8342316 prefixEnd_8342316 4283617879693287883984393 := by
  unfold tailWord_8342316
  simp only [CollatzResearch.WordTrace]
  refine ⟨152134630622610680493719401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202846174163480907324959201 152134630622610680493719401)
  ·
    refine ⟨114100972966958010370289551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152134630622610680493719401 114100972966958010370289551)
    ·
      refine ⟨171151459450437015555434327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114100972966958010370289551 171151459450437015555434327)
      ·
        refine ⟨256727189175655523333151491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171151459450437015555434327 256727189175655523333151491)
        ·
          refine ⟨385090783763483284999727237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256727189175655523333151491 385090783763483284999727237)
          ·
            refine ⟨72204521955653115937448857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 385090783763483284999727237 72204521955653115937448857)
            ·
              refine ⟨54153391466739836953086643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72204521955653115937448857 54153391466739836953086643)
              ·
                refine ⟨81230087200109755429629965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54153391466739836953086643 81230087200109755429629965)
                ·
                  refine ⟨30461282700041158286111237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81230087200109755429629965 30461282700041158286111237)
                  ·
                    refine ⟨5711490506257717178645857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30461282700041158286111237 5711490506257717178645857)
                    ·
                      refine ⟨4283617879693287883984393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711490506257717178645857 4283617879693287883984393)
                      ·
                        rfl

theorem cell23_8342316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 4, 2].length) (baseStart_8342316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342316 prefixEnd_8342316 := by exact prefixLift 8342316
  have htrace : WordTrace (prefixWord ++ tailWord_8342316) baseStart_8342316 baseEnd_8342316 := by
    simpa [prefixWord, tailWord_8342316, baseEnd_8342316] using wordTrace_append hprefix tailTrace_8342316
  have hstable : (prefixWord ++ tailWord_8342316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342316).length < 2 ^ (prefixWord ++ tailWord_8342316).sum := by decide
  have hdescent : baseEnd_8342316 < baseStart_8342316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342379 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 5]
def baseStart_8342379 : Nat := 118140960795 + 8342379 * 2 ^ 59
def prefixEnd_8342379 : Nat := 4983230072969 + 3 ^ 40 * 8342379 * 2
def baseEnd_8342379 : Nat := 4283650228974521137496603

theorem tailTrace_8342379 : CollatzResearch.WordTrace tailWord_8342379 prefixEnd_8342379 4283650228974521137496603 := by
  unfold tailWord_8342379
  simp only [CollatzResearch.WordTrace]
  refine ⟨304271559043993122746982191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202847706029328748497988127 304271559043993122746982191)
  ·
    refine ⟨456407338565989684120473287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304271559043993122746982191 456407338565989684120473287)
    ·
      refine ⟨684611007848984526180709931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456407338565989684120473287 684611007848984526180709931)
      ·
        refine ⟨1026916511773476789271064897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684611007848984526180709931 1026916511773476789271064897)
        ·
          refine ⟨770187383830107591953298673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1026916511773476789271064897 770187383830107591953298673)
          ·
            refine ⟨577640537872580693964974005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770187383830107591953298673 577640537872580693964974005)
            ·
              refine ⟨54153800425554440059216313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 577640537872580693964974005 54153800425554440059216313)
              ·
                refine ⟨40615350319165830044412235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54153800425554440059216313 40615350319165830044412235)
                ·
                  refine ⟨60923025478748745066618353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40615350319165830044412235 60923025478748745066618353)
                  ·
                    refine ⟨45692269109061558799963765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60923025478748745066618353 45692269109061558799963765)
                    ·
                      refine ⟨4283650228974521137496603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45692269109061558799963765 4283650228974521137496603)
                      ·
                        rfl

theorem cell23_8342379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 5].length) (baseStart_8342379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342379 prefixEnd_8342379 := by exact prefixLift 8342379
  have htrace : WordTrace (prefixWord ++ tailWord_8342379) baseStart_8342379 baseEnd_8342379 := by
    simpa [prefixWord, tailWord_8342379, baseEnd_8342379] using wordTrace_append hprefix tailTrace_8342379
  have hstable : (prefixWord ++ tailWord_8342379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342379).length < 2 ^ (prefixWord ++ tailWord_8342379).sum := by decide
  have hdescent : baseEnd_8342379 < baseStart_8342379 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342386 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_8342386 : Nat := 118140960795 + 8342386 * 2 ^ 59
def prefixEnd_8342386 : Nat := 4983230072969 + 3 ^ 40 * 8342386 * 2
def baseEnd_8342386 : Nat := 1427884607779700870036357

theorem tailTrace_8342386 : CollatzResearch.WordTrace tailWord_8342386 prefixEnd_8342386 1427884607779700870036357 := by
  unfold tailWord_8342386
  simp only [CollatzResearch.WordTrace]
  refine ⟨76067953588741940735621753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202847876236645175294991341 76067953588741940735621753)
  ·
    refine ⟨57050965191556455551716315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76067953588741940735621753 57050965191556455551716315)
    ·
      refine ⟨85576447787334683327574473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57050965191556455551716315 85576447787334683327574473)
      ·
        refine ⟨64182335840501012495680855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85576447787334683327574473 64182335840501012495680855)
        ·
          refine ⟨96273503760751518743521283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64182335840501012495680855 96273503760751518743521283)
          ·
            refine ⟨144410255641127278115281925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96273503760751518743521283 144410255641127278115281925)
            ·
              refine ⟨27076922932711364646615361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144410255641127278115281925 27076922932711364646615361)
              ·
                refine ⟨20307692199533523484961521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27076922932711364646615361 20307692199533523484961521)
                ·
                  refine ⟨15230769149650142613721141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20307692199533523484961521 15230769149650142613721141)
                  ·
                    refine ⟨1427884607779700870036357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15230769149650142613721141 1427884607779700870036357)
                    ·
                      rfl

theorem cell23_8342386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_8342386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342386 prefixEnd_8342386 := by exact prefixLift 8342386
  have htrace : WordTrace (prefixWord ++ tailWord_8342386) baseStart_8342386 baseEnd_8342386 := by
    simpa [prefixWord, tailWord_8342386, baseEnd_8342386] using wordTrace_append hprefix tailTrace_8342386
  have hstable : (prefixWord ++ tailWord_8342386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342386).length < 2 ^ (prefixWord ++ tailWord_8342386).sum := by decide
  have hdescent : baseEnd_8342386 < baseStart_8342386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342390 : List Nat := [5, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_8342390 : Nat := 118140960795 + 8342390 * 2 ^ 59
def prefixEnd_8342390 : Nat := 4983230072969 + 3 ^ 40 * 8342390 * 2
def baseEnd_8342390 : Nat := 475961764140191177162117

theorem tailTrace_8342390 : CollatzResearch.WordTrace tailWord_8342390 prefixEnd_8342390 475961764140191177162117 := by
  unfold tailWord_8342390
  simp only [CollatzResearch.WordTrace]
  refine ⟨19016997515434579476602039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202847973497968847750421749 19016997515434579476602039)
  ·
    refine ⟨28525496273151869214903059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19016997515434579476602039 28525496273151869214903059)
    ·
      refine ⟨42788244409727803822354589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28525496273151869214903059 42788244409727803822354589)
      ·
        refine ⟨16045591653647926433382971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42788244409727803822354589 16045591653647926433382971)
        ·
          refine ⟨24068387480471889650074457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16045591653647926433382971 24068387480471889650074457)
          ·
            refine ⟨18051290610353917237555843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24068387480471889650074457 18051290610353917237555843)
            ·
              refine ⟨27076935915530875856333765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18051290610353917237555843 27076935915530875856333765)
              ·
                refine ⟨5076925484162039223062581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27076935915530875856333765 5076925484162039223062581)
                ·
                  refine ⟨475961764140191177162117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5076925484162039223062581 475961764140191177162117)
                  ·
                    rfl

theorem cell23_8342390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_8342390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342390 prefixEnd_8342390 := by exact prefixLift 8342390
  have htrace : WordTrace (prefixWord ++ tailWord_8342390) baseStart_8342390 baseEnd_8342390 := by
    simpa [prefixWord, tailWord_8342390, baseEnd_8342390] using wordTrace_append hprefix tailTrace_8342390
  have hstable : (prefixWord ++ tailWord_8342390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342390).length < 2 ^ (prefixWord ++ tailWord_8342390).sum := by decide
  have hdescent : baseEnd_8342390 < baseStart_8342390 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342419 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 4]
def baseStart_8342419 : Nat := 118140960795 + 8342419 * 2 ^ 59
def prefixEnd_8342419 : Nat := 4983230072969 + 3 ^ 40 * 8342419 * 2
def baseEnd_8342419 : Nat := 4283670768200700980996419

theorem tailTrace_8342419 : CollatzResearch.WordTrace tailWord_8342419 prefixEnd_8342419 4283670768200700980996419 := by
  unfold tailWord_8342419
  simp only [CollatzResearch.WordTrace]
  refine ⟨304273017963848209578438311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202848678642565473052292207 304273017963848209578438311)
  ·
    refine ⟨456409526945772314367657467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304273017963848209578438311 456409526945772314367657467)
    ·
      refine ⟨684614290418658471551486201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456409526945772314367657467 684614290418658471551486201)
      ·
        refine ⟨513460717813993853663614651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684614290418658471551486201 513460717813993853663614651)
        ·
          refine ⟨770191076720990780495421977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513460717813993853663614651 770191076720990780495421977)
          ·
            refine ⟨577643307540743085371566483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770191076720990780495421977 577643307540743085371566483)
            ·
              refine ⟨866464961311114628057349725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577643307540743085371566483 866464961311114628057349725)
              ·
                refine ⟨324924360491667985521506147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 866464961311114628057349725 324924360491667985521506147)
                ·
                  refine ⟨487386540737501978282259221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324924360491667985521506147 487386540737501978282259221)
                  ·
                    refine ⟨22846244097070405231980901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 487386540737501978282259221 22846244097070405231980901)
                    ·
                      refine ⟨4283670768200700980996419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22846244097070405231980901 4283670768200700980996419)
                      ·
                        rfl

theorem cell23_8342419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_8342419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342419 prefixEnd_8342419 := by exact prefixLift 8342419
  have htrace : WordTrace (prefixWord ++ tailWord_8342419) baseStart_8342419 baseEnd_8342419 := by
    simpa [prefixWord, tailWord_8342419, baseEnd_8342419] using wordTrace_append hprefix tailTrace_8342419
  have hstable : (prefixWord ++ tailWord_8342419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342419).length < 2 ^ (prefixWord ++ tailWord_8342419).sum := by decide
  have hdescent : baseEnd_8342419 < baseStart_8342419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342496 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 4]
def baseStart_8342496 : Nat := 118140960795 + 8342496 * 2 ^ 59
def prefixEnd_8342496 : Nat := 4983230072969 + 3 ^ 40 * 8342496 * 2
def baseEnd_8342496 : Nat := 4283710306211097179733565

theorem tailTrace_8342496 : CollatzResearch.WordTrace tailWord_8342496 prefixEnd_8342496 4283710306211097179733565 := by
  unfold tailWord_8342496
  simp only [CollatzResearch.WordTrace]
  refine ⟨152137913192284625864495671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202850550923046167819327561 152137913192284625864495671)
  ·
    refine ⟨228206869788426938796743507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152137913192284625864495671 228206869788426938796743507)
    ·
      refine ⟨342310304682640408195115261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228206869788426938796743507 342310304682640408195115261)
      ·
        refine ⟨128366364255990153073168223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342310304682640408195115261 128366364255990153073168223)
        ·
          refine ⟨192549546383985229609752335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128366364255990153073168223 192549546383985229609752335)
          ·
            refine ⟨288824319575977844414628503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192549546383985229609752335 288824319575977844414628503)
            ·
              refine ⟨433236479363966766621942755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288824319575977844414628503 433236479363966766621942755)
              ·
                refine ⟨649854719045950149932914133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433236479363966766621942755 649854719045950149932914133)
                ·
                  refine ⟨15230969977639456639052675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 649854719045950149932914133 15230969977639456639052675)
                  ·
                    refine ⟨22846454966459184958579013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15230969977639456639052675 22846454966459184958579013)
                    ·
                      refine ⟨4283710306211097179733565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22846454966459184958579013 4283710306211097179733565)
                      ·
                        rfl

theorem cell23_8342496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_8342496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342496 prefixEnd_8342496 := by exact prefixLift 8342496
  have htrace : WordTrace (prefixWord ++ tailWord_8342496) baseStart_8342496 baseEnd_8342496 := by
    simpa [prefixWord, tailWord_8342496, baseEnd_8342496] using wordTrace_append hprefix tailTrace_8342496
  have hstable : (prefixWord ++ tailWord_8342496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342496).length < 2 ^ (prefixWord ++ tailWord_8342496).sum := by decide
  have hdescent : baseEnd_8342496 < baseStart_8342496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342514 : List Nat := [3, 2, 1, 5, 2, 1, 2, 1, 6]
def baseStart_8342514 : Nat := 118140960795 + 8342514 * 2 ^ 59
def prefixEnd_8342514 : Nat := 4983230072969 + 3 ^ 40 * 8342514 * 2
def baseEnd_8342514 : Nat := 475968838762542012145387

theorem tailTrace_8342514 : CollatzResearch.WordTrace tailWord_8342514 prefixEnd_8342514 475968838762542012145387 := by
  unfold tailWord_8342514
  simp only [CollatzResearch.WordTrace]
  refine ⟨76069120724626010200786649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202850988599002693868764397 76069120724626010200786649)
  ·
    refine ⟨57051840543469507650589987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76069120724626010200786649 57051840543469507650589987)
    ·
      refine ⟨85577760815204261475884981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57051840543469507650589987 85577760815204261475884981)
      ·
        refine ⟨8022915076425399513364217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85577760815204261475884981 8022915076425399513364217)
        ·
          refine ⟨6017186307319049635023163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8022915076425399513364217 6017186307319049635023163)
          ·
            refine ⟨9025779460978574452534745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017186307319049635023163 9025779460978574452534745)
            ·
              refine ⟨6769334595733930839401059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9025779460978574452534745 6769334595733930839401059)
              ·
                refine ⟨10154001893600896259101589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6769334595733930839401059 10154001893600896259101589)
                ·
                  refine ⟨475968838762542012145387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10154001893600896259101589 475968838762542012145387)
                  ·
                    rfl

theorem cell23_8342514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_8342514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342514 prefixEnd_8342514 := by exact prefixLift 8342514
  have htrace : WordTrace (prefixWord ++ tailWord_8342514) baseStart_8342514 baseEnd_8342514 := by
    simpa [prefixWord, tailWord_8342514, baseEnd_8342514] using wordTrace_append hprefix tailTrace_8342514
  have hstable : (prefixWord ++ tailWord_8342514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342514).length < 2 ^ (prefixWord ++ tailWord_8342514).sum := by decide
  have hdescent : baseEnd_8342514 < baseStart_8342514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342533 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 3, 2, 3]
def baseStart_8342533 : Nat := 118140960795 + 8342533 * 2 ^ 59
def prefixEnd_8342533 : Nat := 4983230072969 + 3 ^ 40 * 8342533 * 2
def baseEnd_8342533 : Nat := 4283729304995313534970895

theorem tailTrace_8342533 : CollatzResearch.WordTrace tailWord_8342533 prefixEnd_8342533 4283729304995313534970895 := by
  unfold tailWord_8342533
  simp only [CollatzResearch.WordTrace]
  refine ⟨304277175885435207048088253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202851450590290138032058835 304277175885435207048088253)
  ·
    refine ⟨114103940957038202643033095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304277175885435207048088253 114103940957038202643033095)
    ·
      refine ⟨171155911435557303964549643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114103940957038202643033095 171155911435557303964549643)
      ·
        refine ⟨256733867153335955946824465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171155911435557303964549643 256733867153335955946824465)
        ·
          refine ⟨192550400365001966960118349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256733867153335955946824465 192550400365001966960118349)
          ·
            refine ⟨72206400136875737610044381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192550400365001966960118349 72206400136875737610044381)
            ·
              refine ⟨27077400051328401603766643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72206400136875737610044381 27077400051328401603766643)
              ·
                refine ⟨40616100076992602405649965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27077400051328401603766643 40616100076992602405649965)
                ·
                  refine ⟨15231037528872225902118737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40616100076992602405649965 15231037528872225902118737)
                  ·
                    refine ⟨11423278146654169426589053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15231037528872225902118737 11423278146654169426589053)
                    ·
                      refine ⟨4283729304995313534970895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11423278146654169426589053 4283729304995313534970895)
                      ·
                        rfl

theorem cell23_8342533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_8342533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342533 prefixEnd_8342533 := by exact prefixLift 8342533
  have htrace : WordTrace (prefixWord ++ tailWord_8342533) baseStart_8342533 baseEnd_8342533 := by
    simpa [prefixWord, tailWord_8342533, baseEnd_8342533] using wordTrace_append hprefix tailTrace_8342533
  have hstable : (prefixWord ++ tailWord_8342533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342533).length < 2 ^ (prefixWord ++ tailWord_8342533).sum := by decide
  have hdescent : baseEnd_8342533 < baseStart_8342533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342536 : List Nat := [2, 1, 3, 2, 1, 3, 2, 9]
def baseStart_8342536 : Nat := 118140960795 + 8342536 * 2 ^ 59
def prefixEnd_8342536 : Nat := 4983230072969 + 3 ^ 40 * 8342536 * 2
def baseEnd_8342536 : Nat := 158656697979158408267903

theorem tailTrace_8342536 : CollatzResearch.WordTrace tailWord_8342536 prefixEnd_8342536 158656697979158408267903 := by
  unfold tailWord_8342536
  simp only [CollatzResearch.WordTrace]
  refine ⟨152138642652212169280223731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202851523536282892373631641 152138642652212169280223731)
  ·
    refine ⟨228207963978318253920335597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152138642652212169280223731 228207963978318253920335597)
    ·
      refine ⟨85577986491869345220125849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228207963978318253920335597 85577986491869345220125849)
      ·
        refine ⟨64183489868902008915094387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85577986491869345220125849 64183489868902008915094387)
        ·
          refine ⟨96275234803353013372641581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64183489868902008915094387 96275234803353013372641581)
          ·
            refine ⟨36103213051257380014740593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96275234803353013372641581 36103213051257380014740593)
            ·
              refine ⟨27077409788443035011055445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36103213051257380014740593 27077409788443035011055445)
              ·
                refine ⟨158656697979158408267903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27077409788443035011055445 158656697979158408267903)
                ·
                  rfl

theorem cell23_8342536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 9].length) (baseStart_8342536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342536 prefixEnd_8342536 := by exact prefixLift 8342536
  have htrace : WordTrace (prefixWord ++ tailWord_8342536) baseStart_8342536 baseEnd_8342536 := by
    simpa [prefixWord, tailWord_8342536, baseEnd_8342536] using wordTrace_append hprefix tailTrace_8342536
  have hstable : (prefixWord ++ tailWord_8342536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342536).length < 2 ^ (prefixWord ++ tailWord_8342536).sum := by decide
  have hdescent : baseEnd_8342536 < baseStart_8342536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342547 : List Nat := [1, 1, 1, 2, 1, 4, 1, 7, 1, 2, 2]
def baseStart_8342547 : Nat := 118140960795 + 8342547 * 2 ^ 59
def prefixEnd_8342547 : Nat := 4983230072969 + 3 ^ 40 * 8342547 * 2
def baseEnd_8342547 : Nat := 4283736493724476480195831

theorem tailTrace_8342547 : CollatzResearch.WordTrace tailWord_8342547 prefixEnd_8342547 4283736493724476480195831 := by
  unfold tailWord_8342547
  simp only [CollatzResearch.WordTrace]
  refine ⟨304277686507384487439097895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202851791004922991626065263 304277686507384487439097895)
  ·
    refine ⟨456416529761076731158646843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304277686507384487439097895 456416529761076731158646843)
    ·
      refine ⟨684624794641615096737970265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456416529761076731158646843 684624794641615096737970265)
      ·
        refine ⟨513468595981211322553477699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684624794641615096737970265 513468595981211322553477699)
        ·
          refine ⟨770202893971816983830216549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513468595981211322553477699 770202893971816983830216549)
          ·
            refine ⟨144413042619715684468165603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 770202893971816983830216549 144413042619715684468165603)
            ·
              refine ⟨216619563929573526702248405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144413042619715684468165603 216619563929573526702248405)
              ·
                refine ⟨5077021029599379532083947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 216619563929573526702248405 5077021029599379532083947)
                ·
                  refine ⟨7615531544399069298125921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077021029599379532083947 7615531544399069298125921)
                  ·
                    refine ⟨5711648658299301973594441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7615531544399069298125921 5711648658299301973594441)
                    ·
                      refine ⟨4283736493724476480195831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711648658299301973594441 4283736493724476480195831)
                      ·
                        rfl

theorem cell23_8342547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 1, 2, 2].length) (baseStart_8342547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342547 prefixEnd_8342547 := by exact prefixLift 8342547
  have htrace : WordTrace (prefixWord ++ tailWord_8342547) baseStart_8342547 baseEnd_8342547 := by
    simpa [prefixWord, tailWord_8342547, baseEnd_8342547] using wordTrace_append hprefix tailTrace_8342547
  have hstable : (prefixWord ++ tailWord_8342547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342547).length < 2 ^ (prefixWord ++ tailWord_8342547).sum := by decide
  have hdescent : baseEnd_8342547 < baseStart_8342547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342557 : List Nat := [1, 4, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_8342557 : Nat := 118140960795 + 8342557 * 2 ^ 59
def prefixEnd_8342557 : Nat := 4983230072969 + 3 ^ 40 * 8342557 * 2
def baseEnd_8342557 : Nat := 1427913876177007147023595

theorem tailTrace_8342557 : CollatzResearch.WordTrace tailWord_8342557 prefixEnd_8342557 1427913876177007147023595 := by
  unfold tailWord_8342557
  simp only [CollatzResearch.WordTrace]
  refine ⟨304278051237348259146961925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202852034158232172764641283 304278051237348259146961925)
  ·
    refine ⟨57052134607002798590055361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304278051237348259146961925 57052134607002798590055361)
    ·
      refine ⟨42789100955252098942541521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57052134607002798590055361 42789100955252098942541521)
      ·
        refine ⟨32091825716439074206906141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42789100955252098942541521 32091825716439074206906141)
        ·
          refine ⟨12034434643664652827589803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32091825716439074206906141 12034434643664652827589803)
          ·
            refine ⟨18051651965496979241384705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12034434643664652827589803 18051651965496979241384705)
            ·
              refine ⟨13538738974122734431038529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18051651965496979241384705 13538738974122734431038529)
              ·
                refine ⟨10154054230592050823278897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13538738974122734431038529 10154054230592050823278897)
                ·
                  refine ⟨7615540672944038117459173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10154054230592050823278897 7615540672944038117459173)
                  ·
                    refine ⟨1427913876177007147023595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7615540672944038117459173 1427913876177007147023595)
                    ·
                      rfl

theorem cell23_8342557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_8342557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342557 prefixEnd_8342557 := by exact prefixLift 8342557
  have htrace : WordTrace (prefixWord ++ tailWord_8342557) baseStart_8342557 baseEnd_8342557 := by
    simpa [prefixWord, tailWord_8342557, baseEnd_8342557] using wordTrace_append hprefix tailTrace_8342557
  have hstable : (prefixWord ++ tailWord_8342557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342557).length < 2 ^ (prefixWord ++ tailWord_8342557).sum := by decide
  have hdescent : baseEnd_8342557 < baseStart_8342557 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342570 : List Nat := [3, 1, 4, 1, 3, 2, 1, 8]
def baseStart_8342570 : Nat := 118140960795 + 8342570 * 2 ^ 59
def prefixEnd_8342570 : Nat := 4983230072969 + 3 ^ 40 * 8342570 * 2
def baseEnd_8342570 : Nat := 158657344584427032970675

theorem tailTrace_8342570 : CollatzResearch.WordTrace tailWord_8342570 prefixEnd_8342570 158657344584427032970675 := by
  unfold tailWord_8342570
  simp only [CollatzResearch.WordTrace]
  refine ⟨76069631346575290591796291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202852350257534108244790109 76069631346575290591796291)
  ·
    refine ⟨114104447019862935887694437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76069631346575290591796291 114104447019862935887694437)
    ·
      refine ⟨21394583816224300478942707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114104447019862935887694437 21394583816224300478942707)
      ·
        refine ⟨32091875724336450718414061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21394583816224300478942707 32091875724336450718414061)
        ·
          refine ⟨12034453396626169019405273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32091875724336450718414061 12034453396626169019405273)
          ·
            refine ⟨9025840047469626764553955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12034453396626169019405273 9025840047469626764553955)
            ·
              refine ⟨13538760071204440146830933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9025840047469626764553955 13538760071204440146830933)
              ·
                refine ⟨158657344584427032970675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13538760071204440146830933 158657344584427032970675)
                ·
                  rfl

theorem cell23_8342570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 8].length) (baseStart_8342570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342570 prefixEnd_8342570 := by exact prefixLift 8342570
  have htrace : WordTrace (prefixWord ++ tailWord_8342570) baseStart_8342570 baseEnd_8342570 := by
    simpa [prefixWord, tailWord_8342570, baseEnd_8342570] using wordTrace_append hprefix tailTrace_8342570
  have hstable : (prefixWord ++ tailWord_8342570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342570).length < 2 ^ (prefixWord ++ tailWord_8342570).sum := by decide
  have hdescent : baseEnd_8342570 < baseStart_8342570 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342598 : List Nat := [6, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_8342598 : Nat := 118140960795 + 8342598 * 2 ^ 59
def prefixEnd_8342598 : Nat := 4983230072969 + 3 ^ 40 * 8342598 * 2
def baseEnd_8342598 : Nat := 4283762681237855780658097

theorem tailTrace_8342598 : CollatzResearch.WordTrace tailWord_8342598 prefixEnd_8342598 4283762681237855780658097 := by
  unfold tailWord_8342598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9508735832193741348412639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202853031086799815432802965 9508735832193741348412639)
  ·
    refine ⟨14263103748290612022618959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9508735832193741348412639 14263103748290612022618959)
    ·
      refine ⟨21394655622435918033928439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14263103748290612022618959 21394655622435918033928439)
      ·
        refine ⟨32091983433653877050892659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21394655622435918033928439 32091983433653877050892659)
        ·
          refine ⟨48137975150480815576338989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32091983433653877050892659 48137975150480815576338989)
          ·
            refine ⟨18051740681430305841127121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48137975150480815576338989 18051740681430305841127121)
            ·
              refine ⟨13538805511072729380845341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18051740681430305841127121 13538805511072729380845341)
              ·
                refine ⟨5077052066652273517817003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13538805511072729380845341 5077052066652273517817003)
                ·
                  refine ⟨7615578099978410276725505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077052066652273517817003 7615578099978410276725505)
                  ·
                    refine ⟨5711683574983807707544129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7615578099978410276725505 5711683574983807707544129)
                    ·
                      refine ⟨4283762681237855780658097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711683574983807707544129 4283762681237855780658097)
                      ·
                        rfl

theorem cell23_8342598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_8342598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342598 prefixEnd_8342598 := by exact prefixLift 8342598
  have htrace : WordTrace (prefixWord ++ tailWord_8342598) baseStart_8342598 baseEnd_8342598 := by
    simpa [prefixWord, tailWord_8342598, baseEnd_8342598] using wordTrace_append hprefix tailTrace_8342598
  have hstable : (prefixWord ++ tailWord_8342598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342598).length < 2 ^ (prefixWord ++ tailWord_8342598).sum := by decide
  have hdescent : baseEnd_8342598 < baseStart_8342598 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342633 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 2, 2, 4]
def baseStart_8342633 : Nat := 118140960795 + 8342633 * 2 ^ 59
def prefixEnd_8342633 : Nat := 4983230072969 + 3 ^ 40 * 8342633 * 2
def baseEnd_8342633 : Nat := 4283780653060763143720435

theorem tailTrace_8342633 : CollatzResearch.WordTrace tailWord_8342633 prefixEnd_8342633 4283780653060763143720435 := by
  unfold tailWord_8342633
  simp only [CollatzResearch.WordTrace]
  refine ⟨304280823185072924126728553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202853882123381949417819035 304280823185072924126728553)
  ·
    refine ⟨228210617388804693095046415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304280823185072924126728553 228210617388804693095046415)
    ·
      refine ⟨342315926083207039642569623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228210617388804693095046415 342315926083207039642569623)
      ·
        refine ⟨513473889124810559463854435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342315926083207039642569623 513473889124810559463854435)
        ·
          refine ⟨770210833687215839195781653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513473889124810559463854435 770210833687215839195781653)
          ·
            refine ⟨36103632829088242462302265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 770210833687215839195781653 36103632829088242462302265)
            ·
              refine ⟨27077724621816181846726699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36103632829088242462302265 27077724621816181846726699)
              ·
                refine ⟨40616586932724272770090049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27077724621816181846726699 40616586932724272770090049)
                ·
                  refine ⟨30462440199543204577567537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40616586932724272770090049 30462440199543204577567537)
                  ·
                    refine ⟨22846830149657403433175653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30462440199543204577567537 22846830149657403433175653)
                    ·
                      refine ⟨4283780653060763143720435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22846830149657403433175653 4283780653060763143720435)
                      ·
                        rfl

theorem cell23_8342633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_8342633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342633 prefixEnd_8342633 := by exact prefixLift 8342633
  have htrace : WordTrace (prefixWord ++ tailWord_8342633) baseStart_8342633 baseEnd_8342633 := by
    simpa [prefixWord, tailWord_8342633, baseEnd_8342633] using wordTrace_append hprefix tailTrace_8342633
  have hstable : (prefixWord ++ tailWord_8342633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342633).length < 2 ^ (prefixWord ++ tailWord_8342633).sum := by decide
  have hdescent : baseEnd_8342633 < baseStart_8342633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342637 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_8342637 : Nat := 118140960795 + 8342637 * 2 ^ 59
def prefixEnd_8342637 : Nat := 4983230072969 + 3 ^ 40 * 8342637 * 2
def baseEnd_8342637 : Nat := 4283782706983381128070417

theorem tailTrace_8342637 : CollatzResearch.WordTrace tailWord_8342637 prefixEnd_8342637 4283782706983381128070417 := by
  unfold tailWord_8342637
  simp only [CollatzResearch.WordTrace]
  refine ⟨304280969077058432809874165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202853979384705621873249443 304280969077058432809874165)
  ·
    refine ⟨28526340850974228075925703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304280969077058432809874165 28526340850974228075925703)
    ·
      refine ⟨42789511276461342113888555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28526340850974228075925703 42789511276461342113888555)
      ·
        refine ⟨64184266914692013170832833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42789511276461342113888555 64184266914692013170832833)
        ·
          refine ⟨48138200186019009878124625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64184266914692013170832833 48138200186019009878124625)
          ·
            refine ⟨36103650139514257408593469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48138200186019009878124625 36103650139514257408593469)
            ·
              refine ⟨13538868802317846528222551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36103650139514257408593469 13538868802317846528222551)
              ·
                refine ⟨20308303203476769792333827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13538868802317846528222551 20308303203476769792333827)
                ·
                  refine ⟨30462454805215154688500741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20308303203476769792333827 30462454805215154688500741)
                  ·
                    refine ⟨5711710275977841504093889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30462454805215154688500741 5711710275977841504093889)
                    ·
                      refine ⟨4283782706983381128070417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711710275977841504093889 4283782706983381128070417)
                      ·
                        rfl

theorem cell23_8342637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_8342637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342637 prefixEnd_8342637 := by exact prefixLift 8342637
  have htrace : WordTrace (prefixWord ++ tailWord_8342637) baseStart_8342637 baseEnd_8342637 := by
    simpa [prefixWord, tailWord_8342637, baseEnd_8342637] using wordTrace_append hprefix tailTrace_8342637
  have hstable : (prefixWord ++ tailWord_8342637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342637).length < 2 ^ (prefixWord ++ tailWord_8342637).sum := by decide
  have hdescent : baseEnd_8342637 < baseStart_8342637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342820 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_8342820 : Nat := 118140960795 + 8342820 * 2 ^ 59
def prefixEnd_8342820 : Nat := 4983230072969 + 3 ^ 40 * 8342820 * 2
def baseEnd_8342820 : Nat := 4283876673943153912082075

theorem tailTrace_8342820 : CollatzResearch.WordTrace tailWord_8342820 prefixEnd_8342820 4283876673943153912082075 := by
  unfold tailWord_8342820
  simp only [CollatzResearch.WordTrace]
  refine ⟨152143821817697727531892957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202858429090263636709190609 152143821817697727531892957)
  ·
    refine ⟨57053933181636647824459859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152143821817697727531892957 57053933181636647824459859)
    ·
      refine ⟨85580899772454971736689789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57053933181636647824459859 85580899772454971736689789)
      ·
        refine ⟨32092837414670614401258671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85580899772454971736689789 32092837414670614401258671)
        ·
          refine ⟨48139256122005921601888007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32092837414670614401258671 48139256122005921601888007)
          ·
            refine ⟨72208884183008882402832011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48139256122005921601888007 72208884183008882402832011)
            ·
              refine ⟨108313326274513323604248017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72208884183008882402832011 108313326274513323604248017)
              ·
                refine ⟨81234994705884992703186013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108313326274513323604248017 81234994705884992703186013)
                ·
                  refine ⟨30463123014706872263694755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81234994705884992703186013 30463123014706872263694755)
                  ·
                    refine ⟨45694684522060308395542133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30463123014706872263694755 45694684522060308395542133)
                    ·
                      refine ⟨4283876673943153912082075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45694684522060308395542133 4283876673943153912082075)
                      ·
                        rfl

theorem cell23_8342820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_8342820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342820 prefixEnd_8342820 := by exact prefixLift 8342820
  have htrace : WordTrace (prefixWord ++ tailWord_8342820) baseStart_8342820 baseEnd_8342820 := by
    simpa [prefixWord, tailWord_8342820, baseEnd_8342820] using wordTrace_append hprefix tailTrace_8342820
  have hstable : (prefixWord ++ tailWord_8342820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342820).length < 2 ^ (prefixWord ++ tailWord_8342820).sum := by decide
  have hdescent : baseEnd_8342820 < baseStart_8342820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342837 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_8342837 : Nat := 118140960795 + 8342837 * 2 ^ 59
def prefixEnd_8342837 : Nat := 4983230072969 + 3 ^ 40 * 8342837 * 2
def baseEnd_8342837 : Nat := 4283885403114280345569497

theorem tailTrace_8342837 : CollatzResearch.WordTrace tailWord_8342837 prefixEnd_8342837 4283885403114280345569497 := by
  unfold tailWord_8342837
  simp only [CollatzResearch.WordTrace]
  refine ⟨304288263676333866967154765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202858842450889244644769843 304288263676333866967154765)
  ·
    refine ⟨114108098878625200112683037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304288263676333866967154765 114108098878625200112683037)
    ·
      refine ⟨42790537079484450042256139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114108098878625200112683037 42790537079484450042256139)
      ·
        refine ⟨64185805619226675063384209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42790537079484450042256139 64185805619226675063384209)
        ·
          refine ⟨48139354214420006297538157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64185805619226675063384209 48139354214420006297538157)
          ·
            refine ⟨18052257830407502361576809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48139354214420006297538157 18052257830407502361576809)
            ·
              refine ⟨13539193372805626771182607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18052257830407502361576809 13539193372805626771182607)
              ·
                refine ⟨20308790059208440156773911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13539193372805626771182607 20308790059208440156773911)
                ·
                  refine ⟨30463185088812660235160867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20308790059208440156773911 30463185088812660235160867)
                  ·
                    refine ⟨45694777633218990352741301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30463185088812660235160867 45694777633218990352741301)
                    ·
                      refine ⟨4283885403114280345569497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45694777633218990352741301 4283885403114280345569497)
                      ·
                        rfl

theorem cell23_8342837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_8342837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342837 prefixEnd_8342837 := by exact prefixLift 8342837
  have htrace : WordTrace (prefixWord ++ tailWord_8342837) baseStart_8342837 baseEnd_8342837 := by
    simpa [prefixWord, tailWord_8342837, baseEnd_8342837] using wordTrace_append hprefix tailTrace_8342837
  have hstable : (prefixWord ++ tailWord_8342837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342837).length < 2 ^ (prefixWord ++ tailWord_8342837).sum := by decide
  have hdescent : baseEnd_8342837 < baseStart_8342837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342838 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_8342838 : Nat := 118140960795 + 8342838 * 2 ^ 59
def prefixEnd_8342838 : Nat := 4983230072969 + 3 ^ 40 * 8342838 * 2
def baseEnd_8342838 : Nat := 4283885916594934841656993

theorem tailTrace_8342838 : CollatzResearch.WordTrace tailWord_8342838 prefixEnd_8342838 4283885916594934841656993 := by
  unfold tailWord_8342838
  simp only [CollatzResearch.WordTrace]
  refine ⟨19018018759333140258621323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202858866766220162758627445 19018018759333140258621323)
  ·
    refine ⟨28527028138999710387931985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19018018759333140258621323 28527028138999710387931985)
    ·
      refine ⟨21395271104249782790948989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28527028138999710387931985 21395271104249782790948989)
      ·
        refine ⟨8023226664093668546605871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21395271104249782790948989 8023226664093668546605871)
        ·
          refine ⟨12034839996140502819908807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8023226664093668546605871 12034839996140502819908807)
          ·
            refine ⟨18052259994210754229863211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12034839996140502819908807 18052259994210754229863211)
            ·
              refine ⟨27078389991316131344794817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18052259994210754229863211 27078389991316131344794817)
              ·
                refine ⟨20308792493487098508596113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27078389991316131344794817 20308792493487098508596113)
                ·
                  refine ⟨15231594370115323881447085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20308792493487098508596113 15231594370115323881447085)
                  ·
                    refine ⟨5711847888793246455542657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15231594370115323881447085 5711847888793246455542657)
                    ·
                      refine ⟨4283885916594934841656993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711847888793246455542657 4283885916594934841656993)
                      ·
                        rfl

theorem cell23_8342838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_8342838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342838 prefixEnd_8342838 := by exact prefixLift 8342838
  have htrace : WordTrace (prefixWord ++ tailWord_8342838) baseStart_8342838 baseEnd_8342838 := by
    simpa [prefixWord, tailWord_8342838, baseEnd_8342838] using wordTrace_append hprefix tailTrace_8342838
  have hstable : (prefixWord ++ tailWord_8342838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342838).length < 2 ^ (prefixWord ++ tailWord_8342838).sum := by decide
  have hdescent : baseEnd_8342838 < baseStart_8342838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342845 : List Nat := [1, 4, 1, 5, 1, 1, 3, 2, 1, 1, 3]
def baseStart_8342845 : Nat := 118140960795 + 8342845 * 2 ^ 59
def prefixEnd_8342845 : Nat := 4983230072969 + 3 ^ 40 * 8342845 * 2
def baseEnd_8342845 : Nat := 4283889510959516314269461

theorem tailTrace_8342845 : CollatzResearch.WordTrace tailWord_8342845 prefixEnd_8342845 4283889510959516314269461 := by
  unfold tailWord_8342845
  simp only [CollatzResearch.WordTrace]
  refine ⟨304288555460304884333445989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202859036973536589555630659 304288555460304884333445989)
  ·
    refine ⟨57054104148807165812521123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304288555460304884333445989 57054104148807165812521123)
    ·
      refine ⟨85581156223210748718781685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57054104148807165812521123 85581156223210748718781685)
      ·
        refine ⟨8023233395926007692385783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85581156223210748718781685 8023233395926007692385783)
        ·
          refine ⟨12034850093889011538578675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8023233395926007692385783 12034850093889011538578675)
          ·
            refine ⟨18052275140833517307868013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12034850093889011538578675 18052275140833517307868013)
            ·
              refine ⟨6769603177812568990450505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18052275140833517307868013 6769603177812568990450505)
              ·
                refine ⟨5077202383359426742837879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6769603177812568990450505 5077202383359426742837879)
                ·
                  refine ⟨7615803575039140114256819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077202383359426742837879 7615803575039140114256819)
                  ·
                    refine ⟨11423705362558710171385229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7615803575039140114256819 11423705362558710171385229)
                    ·
                      refine ⟨4283889510959516314269461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11423705362558710171385229 4283889510959516314269461)
                      ·
                        rfl

theorem cell23_8342845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_8342845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342845 prefixEnd_8342845 := by exact prefixLift 8342845
  have htrace : WordTrace (prefixWord ++ tailWord_8342845) baseStart_8342845 baseEnd_8342845 := by
    simpa [prefixWord, tailWord_8342845, baseEnd_8342845] using wordTrace_append hprefix tailTrace_8342845
  have hstable : (prefixWord ++ tailWord_8342845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342845).length < 2 ^ (prefixWord ++ tailWord_8342845).sum := by decide
  have hdescent : baseEnd_8342845 < baseStart_8342845 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342907 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 3, 4, 2]
def baseStart_8342907 : Nat := 118140960795 + 8342907 * 2 ^ 59
def prefixEnd_8342907 : Nat := 4983230072969 + 3 ^ 40 * 8342907 * 2
def baseEnd_8342907 : Nat := 4283921346760095071694175

theorem tailTrace_8342907 : CollatzResearch.WordTrace tailWord_8342907 prefixEnd_8342907 4283921346760095071694175 := by
  unfold tailWord_8342907
  simp only [CollatzResearch.WordTrace]
  refine ⟨304290816786080268922202975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202860544524053512614801983 304290816786080268922202975)
  ·
    refine ⟨456436225179120403383304463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304290816786080268922202975 456436225179120403383304463)
    ·
      refine ⟨684654337768680605074956695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456436225179120403383304463 684654337768680605074956695)
      ·
        refine ⟨1026981506653020907612435043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684654337768680605074956695 1026981506653020907612435043)
        ·
          refine ⟨1540472259979531361418652565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026981506653020907612435043 1540472259979531361418652565)
          ·
            refine ⟨72209637186540532566499339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1540472259979531361418652565 72209637186540532566499339)
            ·
              refine ⟨108314455779810798849749009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72209637186540532566499339 108314455779810798849749009)
              ·
                refine ⟨81235841834858099137311757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108314455779810798849749009 81235841834858099137311757)
                ·
                  refine ⟨30463440688071787176491909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81235841834858099137311757 30463440688071787176491909)
                  ·
                    refine ⟨5711895129013460095592233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30463440688071787176491909 5711895129013460095592233)
                    ·
                      refine ⟨4283921346760095071694175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711895129013460095592233 4283921346760095071694175)
                      ·
                        rfl

theorem cell23_8342907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 4, 2].length) (baseStart_8342907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342907 prefixEnd_8342907 := by exact prefixLift 8342907
  have htrace : WordTrace (prefixWord ++ tailWord_8342907) baseStart_8342907 baseEnd_8342907 := by
    simpa [prefixWord, tailWord_8342907, baseEnd_8342907] using wordTrace_append hprefix tailTrace_8342907
  have hstable : (prefixWord ++ tailWord_8342907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342907).length < 2 ^ (prefixWord ++ tailWord_8342907).sum := by decide
  have hdescent : baseEnd_8342907 < baseStart_8342907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342924 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 1, 4, 2]
def baseStart_8342924 : Nat := 118140960795 + 8342924 * 2 ^ 59
def prefixEnd_8342924 : Nat := 4983230072969 + 3 ^ 40 * 8342924 * 2
def baseEnd_8342924 : Nat := 4283930075931221505181597

theorem tailTrace_8342924 : CollatzResearch.WordTrace tailWord_8342924 prefixEnd_8342924 4283930075931221505181597 := by
  unfold tailWord_8342924
  simp only [CollatzResearch.WordTrace]
  refine ⟨152145718413509340412785913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202860957884679120550381217 152145718413509340412785913)
  ·
    refine ⟨114109288810132005309589435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152145718413509340412785913 114109288810132005309589435)
    ·
      refine ⟨171163933215198007964384153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114109288810132005309589435 171163933215198007964384153)
      ·
        refine ⟨128372949911398505973288115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171163933215198007964384153 128372949911398505973288115)
        ·
          refine ⟨192559424867097758959932173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128372949911398505973288115 192559424867097758959932173)
          ·
            refine ⟨72209784325161659609974565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192559424867097758959932173 72209784325161659609974565)
            ·
              refine ⟨13539334560967811176870231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72209784325161659609974565 13539334560967811176870231)
              ·
                refine ⟨20309001841451716765305347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13539334560967811176870231 20309001841451716765305347)
                ·
                  refine ⟨30463502762177575147958021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20309001841451716765305347 30463502762177575147958021)
                  ·
                    refine ⟨5711906767908295340242129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30463502762177575147958021 5711906767908295340242129)
                    ·
                      refine ⟨4283930075931221505181597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5711906767908295340242129 4283930075931221505181597)
                      ·
                        rfl

theorem cell23_8342924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_8342924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342924 prefixEnd_8342924 := by exact prefixLift 8342924
  have htrace : WordTrace (prefixWord ++ tailWord_8342924) baseStart_8342924 baseEnd_8342924 := by
    simpa [prefixWord, tailWord_8342924, baseEnd_8342924] using wordTrace_append hprefix tailTrace_8342924
  have hstable : (prefixWord ++ tailWord_8342924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342924).length < 2 ^ (prefixWord ++ tailWord_8342924).sum := by decide
  have hdescent : baseEnd_8342924 < baseStart_8342924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342997 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_8342997 : Nat := 118140960795 + 8342997 * 2 ^ 59
def prefixEnd_8342997 : Nat := 4983230072969 + 3 ^ 40 * 8342997 * 2
def baseEnd_8342997 : Nat := 4283967560018999719568761

theorem tailTrace_8342997 : CollatzResearch.WordTrace tailWord_8342997 prefixEnd_8342997 4283967560018999719568761 := by
  unfold tailWord_8342997
  simp only [CollatzResearch.WordTrace]
  refine ⟨304294099355754214292979245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202862732903836142861986163 304294099355754214292979245)
  ·
    refine ⟨114110287258407830359867217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304294099355754214292979245 114110287258407830359867217)
    ·
      refine ⟨85582715443805872769900413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114110287258407830359867217 85582715443805872769900413)
      ·
        refine ⟨32093518291427202288712655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85582715443805872769900413 32093518291427202288712655)
        ·
          refine ⟨48140277437140803433068983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32093518291427202288712655 48140277437140803433068983)
          ·
            refine ⟨72210416155711205149603475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48140277437140803433068983 72210416155711205149603475)
            ·
              refine ⟨108315624233566807724405213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72210416155711205149603475 108315624233566807724405213)
              ·
                refine ⟨40618359087587552896651955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108315624233566807724405213 40618359087587552896651955)
                ·
                  refine ⟨60927538631381329344977933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40618359087587552896651955 60927538631381329344977933)
                  ·
                    refine ⟨22847826986767998504366725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60927538631381329344977933 22847826986767998504366725)
                    ·
                      refine ⟨4283967560018999719568761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22847826986767998504366725 4283967560018999719568761)
                      ·
                        rfl

theorem cell23_8342997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_8342997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342997 prefixEnd_8342997 := by exact prefixLift 8342997
  have htrace : WordTrace (prefixWord ++ tailWord_8342997) baseStart_8342997 baseEnd_8342997 := by
    simpa [prefixWord, tailWord_8342997, baseEnd_8342997] using wordTrace_append hprefix tailTrace_8342997
  have hstable : (prefixWord ++ tailWord_8342997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342997).length < 2 ^ (prefixWord ++ tailWord_8342997).sum := by decide
  have hdescent : baseEnd_8342997 < baseStart_8342997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8342998 : List Nat := [5, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_8342998 : Nat := 118140960795 + 8342998 * 2 ^ 59
def prefixEnd_8342998 : Nat := 4983230072969 + 3 ^ 40 * 8342998 * 2
def baseEnd_8342998 : Nat := 475996452611072690628473

theorem tailTrace_8342998 : CollatzResearch.WordTrace tailWord_8342998 prefixEnd_8342998 475996452611072690628473 := by
  unfold tailWord_8342998
  simp only [CollatzResearch.WordTrace]
  refine ⟨19018383489296911966485353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202862757219167060975843765 19018383489296911966485353)
  ·
    refine ⟨14263787616972683974864015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19018383489296911966485353 14263787616972683974864015)
    ·
      refine ⟨21395681425459025962296023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14263787616972683974864015 21395681425459025962296023)
      ·
        refine ⟨32093522138188538943444035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21395681425459025962296023 32093522138188538943444035)
        ·
          refine ⟨48140283207282808415166053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32093522138188538943444035 48140283207282808415166053)
          ·
            refine ⟨9026303101365526577843635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48140283207282808415166053 9026303101365526577843635)
            ·
              refine ⟨13539454652048289866765453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9026303101365526577843635 13539454652048289866765453)
              ·
                refine ⟨5077295494518108700037045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13539454652048289866765453 5077295494518108700037045)
                ·
                  refine ⟨475996452611072690628473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5077295494518108700037045 475996452611072690628473)
                  ·
                    rfl

theorem cell23_8342998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_8342998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8342998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8342998 prefixEnd_8342998 := by exact prefixLift 8342998
  have htrace : WordTrace (prefixWord ++ tailWord_8342998) baseStart_8342998 baseEnd_8342998 := by
    simpa [prefixWord, tailWord_8342998, baseEnd_8342998] using wordTrace_append hprefix tailTrace_8342998
  have hstable : (prefixWord ++ tailWord_8342998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8342998).length < 2 ^ (prefixWord ++ tailWord_8342998).sum := by decide
  have hdescent : baseEnd_8342998 < baseStart_8342998 := by decide
  rcases family_descends (prefixWord ++ tailWord_8342998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343024 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 3, 4]
def baseStart_8343024 : Nat := 118140960795 + 8343024 * 2 ^ 59
def prefixEnd_8343024 : Nat := 4983230072969 + 3 ^ 40 * 8343024 * 2
def baseEnd_8343024 : Nat := 1427993807998890371310379

theorem tailTrace_8343024 : CollatzResearch.WordTrace tailWord_8343024 prefixEnd_8343024 1427993807998890371310379 := by
  unfold tailWord_8343024
  simp only [CollatzResearch.WordTrace]
  refine ⟨152147542063328198952106063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202863389417770931936141417 152147542063328198952106063)
  ·
    refine ⟨228221313094992298428159095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152147542063328198952106063 228221313094992298428159095)
    ·
      refine ⟨342331969642488447642238643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228221313094992298428159095 342331969642488447642238643)
      ·
        refine ⟨513497954463732671463357965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342331969642488447642238643 513497954463732671463357965)
        ·
          refine ⟨192561732923899751798759237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513497954463732671463357965 192561732923899751798759237)
          ·
            refine ⟨36105324923231203462267357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192561732923899751798759237 36105324923231203462267357)
            ·
              refine ⟨13539496846211701298350259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36105324923231203462267357 13539496846211701298350259)
              ·
                refine ⟨20309245269317551947525389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13539496846211701298350259 20309245269317551947525389)
                ·
                  refine ⟨7615966975994081980322021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20309245269317551947525389 7615966975994081980322021)
                  ·
                    refine ⟨1427993807998890371310379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7615966975994081980322021 1427993807998890371310379)
                    ·
                      rfl

theorem cell23_8343024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 3, 4].length) (baseStart_8343024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343024 prefixEnd_8343024 := by exact prefixLift 8343024
  have htrace : WordTrace (prefixWord ++ tailWord_8343024) baseStart_8343024 baseEnd_8343024 := by
    simpa [prefixWord, tailWord_8343024, baseEnd_8343024] using wordTrace_append hprefix tailTrace_8343024
  have hstable : (prefixWord ++ tailWord_8343024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343024).length < 2 ^ (prefixWord ++ tailWord_8343024).sum := by decide
  have hdescent : baseEnd_8343024 < baseStart_8343024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343051 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 3]
def baseStart_8343051 : Nat := 118140960795 + 8343051 * 2 ^ 59
def prefixEnd_8343051 : Nat := 4983230072969 + 3 ^ 40 * 8343051 * 2
def baseEnd_8343051 : Nat := 4283995287974342508293513

theorem tailTrace_8343051 : CollatzResearch.WordTrace tailWord_8343051 prefixEnd_8343051 4283995287974342508293513 := by
  unfold tailWord_8343051
  simp only [CollatzResearch.WordTrace]
  refine ⟨304296068897558581515445007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202864045931705721010296671 304296068897558581515445007)
  ·
    refine ⟨456444103346337872273167511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304296068897558581515445007 456444103346337872273167511)
    ·
      refine ⟨684666155019506808409751267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456444103346337872273167511 684666155019506808409751267)
      ·
        refine ⟨1026999232529260212614626901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684666155019506808409751267 1026999232529260212614626901)
        ·
          refine ⟨12035147256202268116577659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 1026999232529260212614626901 12035147256202268116577659)
          ·
            refine ⟨18052720884303402174866489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12035147256202268116577659 18052720884303402174866489)
            ·
              refine ⟨13539540663227551631149867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18052720884303402174866489 13539540663227551631149867)
              ·
                refine ⟨20309310994841327446724801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13539540663227551631149867 20309310994841327446724801)
                ·
                  refine ⟨15231983246130995585043601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20309310994841327446724801 15231983246130995585043601)
                  ·
                    refine ⟨11423987434598246688782701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15231983246130995585043601 11423987434598246688782701)
                    ·
                      refine ⟨4283995287974342508293513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11423987434598246688782701 4283995287974342508293513)
                      ·
                        rfl

theorem cell23_8343051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 3].length) (baseStart_8343051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343051 prefixEnd_8343051 := by exact prefixLift 8343051
  have htrace : WordTrace (prefixWord ++ tailWord_8343051) baseStart_8343051 baseEnd_8343051 := by
    simpa [prefixWord, tailWord_8343051, baseEnd_8343051] using wordTrace_append hprefix tailTrace_8343051
  have hstable : (prefixWord ++ tailWord_8343051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343051).length < 2 ^ (prefixWord ++ tailWord_8343051).sum := by decide
  have hdescent : baseEnd_8343051 < baseStart_8343051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343075 : List Nat := [1, 1, 1, 4, 5, 2, 2, 2, 1, 4]
def baseStart_8343075 : Nat := 118140960795 + 8343075 * 2 ^ 59
def prefixEnd_8343075 : Nat := 4983230072969 + 3 ^ 40 * 8343075 * 2
def baseEnd_8343075 : Nat := 1428002537170016804797801

theorem tailTrace_8343075 : CollatzResearch.WordTrace tailWord_8343075 prefixEnd_8343075 1428002537170016804797801 := by
  unfold tailWord_8343075
  simp only [CollatzResearch.WordTrace]
  refine ⟨304296944249471633614318679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202864629499647755742879119 304296944249471633614318679)
  ·
    refine ⟨456445416374207450421478019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304296944249471633614318679 456445416374207450421478019)
    ·
      refine ⟨684668124561311175632217029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456445416374207450421478019 684668124561311175632217029)
      ·
        refine ⟨128375273355245845431040693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 684668124561311175632217029 128375273355245845431040693)
        ·
          refine ⟨12035181877054298009160065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128375273355245845431040693 12035181877054298009160065)
          ·
            refine ⟨9026386407790723506870049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12035181877054298009160065 9026386407790723506870049)
            ·
              refine ⟨6769789805843042630152537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9026386407790723506870049 6769789805843042630152537)
              ·
                refine ⟨5077342354382281972614403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6769789805843042630152537 5077342354382281972614403)
                ·
                  refine ⟨7616013531573422958921605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077342354382281972614403 7616013531573422958921605)
                  ·
                    refine ⟨1428002537170016804797801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7616013531573422958921605 1428002537170016804797801)
                    ·
                      rfl

theorem cell23_8343075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 1, 4].length) (baseStart_8343075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343075 prefixEnd_8343075 := by exact prefixLift 8343075
  have htrace : WordTrace (prefixWord ++ tailWord_8343075) baseStart_8343075 baseEnd_8343075 := by
    simpa [prefixWord, tailWord_8343075, baseEnd_8343075] using wordTrace_append hprefix tailTrace_8343075
  have hstable : (prefixWord ++ tailWord_8343075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343075).length < 2 ^ (prefixWord ++ tailWord_8343075).sum := by decide
  have hdescent : baseEnd_8343075 < baseStart_8343075 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343104 : List Nat := [2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 4]
def baseStart_8343104 : Nat := 118140960795 + 8343104 * 2 ^ 59
def prefixEnd_8343104 : Nat := 4983230072969 + 3 ^ 40 * 8343104 * 2
def baseEnd_8343104 : Nat := 4284022502449030800930769

theorem tailTrace_8343104 : CollatzResearch.WordTrace tailWord_8343104 prefixEnd_8343104 4284022502449030800930769 := by
  unfold tailWord_8343104
  simp only [CollatzResearch.WordTrace]
  refine ⟨152149000983183285783562183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202865334644244381044749577 152149000983183285783562183)
  ·
    refine ⟨228223501474774928675343275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152149000983183285783562183 228223501474774928675343275)
    ·
      refine ⟨342335252212162393013014913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228223501474774928675343275 342335252212162393013014913)
      ·
        refine ⟨256751439159121794759761185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342335252212162393013014913 256751439159121794759761185)
        ·
          refine ⟨192563579369341346069820889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256751439159121794759761185 192563579369341346069820889)
          ·
            refine ⟨144422684527006009552365667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192563579369341346069820889 144422684527006009552365667)
            ·
              refine ⟨216634026790509014328548501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144422684527006009552365667 216634026790509014328548501)
              ·
                refine ⟨10154720005805110046650711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 216634026790509014328548501 10154720005805110046650711)
                ·
                  refine ⟨15232080008707665069976067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10154720005805110046650711 15232080008707665069976067)
                  ·
                    refine ⟨22848120013061497604964101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15232080008707665069976067 22848120013061497604964101)
                    ·
                      refine ⟨4284022502449030800930769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22848120013061497604964101 4284022502449030800930769)
                      ·
                        rfl

theorem cell23_8343104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_8343104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343104 prefixEnd_8343104 := by exact prefixLift 8343104
  have htrace : WordTrace (prefixWord ++ tailWord_8343104) baseStart_8343104 baseEnd_8343104 := by
    simpa [prefixWord, tailWord_8343104, baseEnd_8343104] using wordTrace_append hprefix tailTrace_8343104
  have hstable : (prefixWord ++ tailWord_8343104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343104).length < 2 ^ (prefixWord ++ tailWord_8343104).sum := by decide
  have hdescent : baseEnd_8343104 < baseStart_8343104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343114 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 4, 4]
def baseStart_8343114 : Nat := 118140960795 + 8343114 * 2 ^ 59
def prefixEnd_8343114 : Nat := 4983230072969 + 3 ^ 40 * 8343114 * 2
def baseEnd_8343114 : Nat := 1428009212418525253935241

theorem tailTrace_8343114 : CollatzResearch.WordTrace tailWord_8343114 prefixEnd_8343114 1428009212418525253935241 := by
  unfold tailWord_8343114
  simp only [CollatzResearch.WordTrace]
  refine ⟨76074591674082585818747099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202865577797553562183325597 76074591674082585818747099)
  ·
    refine ⟨114111887511123878728120649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76074591674082585818747099 114111887511123878728120649)
    ·
      refine ⟨85583915633342909046090487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114111887511123878728120649 85583915633342909046090487)
      ·
        refine ⟨128375873450014363569135731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85583915633342909046090487 128375873450014363569135731)
        ·
          refine ⟨192563810175021545353703597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128375873450014363569135731 192563810175021545353703597)
          ·
            refine ⟨72211428815633079507638849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192563810175021545353703597 72211428815633079507638849)
            ·
              refine ⟨54158571611724809630729137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72211428815633079507638849 54158571611724809630729137)
              ·
                refine ⟨40618928708793607223046853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54158571611724809630729137 40618928708793607223046853)
                ·
                  refine ⟨7616049132898801354321285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40618928708793607223046853 7616049132898801354321285)
                  ·
                    refine ⟨1428009212418525253935241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7616049132898801354321285 1428009212418525253935241)
                    ·
                      rfl

theorem cell23_8343114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_8343114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343114 prefixEnd_8343114 := by exact prefixLift 8343114
  have htrace : WordTrace (prefixWord ++ tailWord_8343114) baseStart_8343114 baseEnd_8343114 := by
    simpa [prefixWord, tailWord_8343114, baseEnd_8343114] using wordTrace_append hprefix tailTrace_8343114
  have hstable : (prefixWord ++ tailWord_8343114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343114).length < 2 ^ (prefixWord ++ tailWord_8343114).sum := by decide
  have hdescent : baseEnd_8343114 < baseStart_8343114 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343121 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 5, 2, 2]
def baseStart_8343121 : Nat := 118140960795 + 8343121 * 2 ^ 59
def prefixEnd_8343121 : Nat := 4983230072969 + 3 ^ 40 * 8343121 * 2
def baseEnd_8343121 : Nat := 4284031231620157234418191

theorem tailTrace_8343121 : CollatzResearch.WordTrace tailWord_8343121 prefixEnd_8343121 4284031231620157234418191 := by
  unfold tailWord_8343121
  simp only [CollatzResearch.WordTrace]
  refine ⟨304298622007304983470493217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202865748004869988980328811 304298622007304983470493217)
  ·
    refine ⟨228223966505478737602869913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304298622007304983470493217 228223966505478737602869913)
    ·
      refine ⟨171167974879109053202152435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228223966505478737602869913 171167974879109053202152435)
      ·
        refine ⟨256751962318663579803228653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171167974879109053202152435 256751962318663579803228653)
        ·
          refine ⟨96281985869498842426210745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256751962318663579803228653 96281985869498842426210745)
          ·
            refine ⟨72211489402124131819658059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96281985869498842426210745 72211489402124131819658059)
            ·
              refine ⟨108317234103186197729487089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72211489402124131819658059 108317234103186197729487089)
              ·
                refine ⟨81237925577389648297115317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108317234103186197729487089 81237925577389648297115317)
                ·
                  refine ⟨7616055522880279527854561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81237925577389648297115317 7616055522880279527854561)
                  ·
                    refine ⟨5712041642160209645890921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7616055522880279527854561 5712041642160209645890921)
                    ·
                      refine ⟨4284031231620157234418191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5712041642160209645890921 4284031231620157234418191)
                      ·
                        rfl

theorem cell23_8343121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 2, 2].length) (baseStart_8343121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343121 prefixEnd_8343121 := by exact prefixLift 8343121
  have htrace : WordTrace (prefixWord ++ tailWord_8343121) baseStart_8343121 baseEnd_8343121 := by
    simpa [prefixWord, tailWord_8343121, baseEnd_8343121] using wordTrace_append hprefix tailTrace_8343121
  have hstable : (prefixWord ++ tailWord_8343121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343121).length < 2 ^ (prefixWord ++ tailWord_8343121).sum := by decide
  have hdescent : baseEnd_8343121 < baseStart_8343121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343124 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_8343124 : Nat := 118140960795 + 8343124 * 2 ^ 59
def prefixEnd_8343124 : Nat := 4983230072969 + 3 ^ 40 * 8343124 * 2
def baseEnd_8343124 : Nat := 4284032772062120722680677

theorem tailTrace_8343124 : CollatzResearch.WordTrace tailWord_8343124 prefixEnd_8343124 4284032772062120722680677 := by
  unfold tailWord_8343124
  simp only [CollatzResearch.WordTrace]
  refine ⟨152149365713147057491426213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202865820950862743321901617 152149365713147057491426213)
  ·
    refine ⟨28528006071215073279642415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152149365713147057491426213 28528006071215073279642415)
    ·
      refine ⟨42792009106822609919463623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28528006071215073279642415 42792009106822609919463623)
      ·
        refine ⟨64188013660233914879195435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42792009106822609919463623 64188013660233914879195435)
        ·
          refine ⟨96282020490350872318793153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64188013660233914879195435 96282020490350872318793153)
          ·
            refine ⟨72211515367763154239094865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96282020490350872318793153 72211515367763154239094865)
            ·
              refine ⟨54158636525822365679321149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72211515367763154239094865 54158636525822365679321149)
              ·
                refine ⟨20309488697183387129745431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54158636525822365679321149 20309488697183387129745431)
                ·
                  refine ⟨30464233045775080694618147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20309488697183387129745431 30464233045775080694618147)
                  ·
                    refine ⟨45696349568662621041927221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30464233045775080694618147 45696349568662621041927221)
                    ·
                      refine ⟨4284032772062120722680677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45696349568662621041927221 4284032772062120722680677)
                      ·
                        rfl

theorem cell23_8343124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_8343124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343124 prefixEnd_8343124 := by exact prefixLift 8343124
  have htrace : WordTrace (prefixWord ++ tailWord_8343124) baseStart_8343124 baseEnd_8343124 := by
    simpa [prefixWord, tailWord_8343124, baseEnd_8343124] using wordTrace_append hprefix tailTrace_8343124
  have hstable : (prefixWord ++ tailWord_8343124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343124).length < 2 ^ (prefixWord ++ tailWord_8343124).sum := by decide
  have hdescent : baseEnd_8343124 < baseStart_8343124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343127 : List Nat := [1, 1, 3, 2, 2, 4, 10]
def baseStart_8343127 : Nat := 118140960795 + 8343127 * 2 ^ 59
def prefixEnd_8343127 : Nat := 4983230072969 + 3 ^ 40 * 8343127 * 2
def baseEnd_8343127 : Nat := 52889312500050422357323

theorem tailTrace_8343127 : CollatzResearch.WordTrace tailWord_8343127 prefixEnd_8343127 52889312500050422357323 := by
  unfold tailWord_8343127
  simp only [CollatzResearch.WordTrace]
  refine ⟨304298840845283246495211635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202865893896855497663474423 304298840845283246495211635)
  ·
    refine ⟨456448261267924869742817453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304298840845283246495211635 456448261267924869742817453)
    ·
      refine ⟨171168097975471826153556545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456448261267924869742817453 171168097975471826153556545)
      ·
        refine ⟨128376073481603869615167409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171168097975471826153556545 128376073481603869615167409)
        ·
          refine ⟨96282055111202902211375557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128376073481603869615167409 96282055111202902211375557)
          ·
            refine ⟨18052885333350544164632917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96282055111202902211375557 18052885333350544164632917)
            ·
              refine ⟨52889312500050422357323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 18052885333350544164632917 52889312500050422357323)
              ·
                rfl

theorem cell23_8343127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 10].length) (baseStart_8343127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343127 prefixEnd_8343127 := by exact prefixLift 8343127
  have htrace : WordTrace (prefixWord ++ tailWord_8343127) baseStart_8343127 baseEnd_8343127 := by
    simpa [prefixWord, tailWord_8343127, baseEnd_8343127] using wordTrace_append hprefix tailTrace_8343127
  have hstable : (prefixWord ++ tailWord_8343127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343127).length < 2 ^ (prefixWord ++ tailWord_8343127).sum := by decide
  have hdescent : baseEnd_8343127 < baseStart_8343127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343158 : List Nat := [5, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_8343158 : Nat := 118140960795 + 8343158 * 2 ^ 59
def prefixEnd_8343158 : Nat := 4983230072969 + 3 ^ 40 * 8343158 * 2
def baseEnd_8343158 : Nat := 4284050230404373589655521

theorem tailTrace_8343158 : CollatzResearch.WordTrace tailWord_8343158 prefixEnd_8343158 4284050230404373589655521 := by
  unfold tailWord_8343158
  simp only [CollatzResearch.WordTrace]
  refine ⟨19018748219260683674349383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202866647672113959193060085 19018748219260683674349383)
  ·
    refine ⟨28528122328891025511524075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19018748219260683674349383 28528122328891025511524075)
    ·
      refine ⟨42792183493336538267286113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28528122328891025511524075 42792183493336538267286113)
      ·
        refine ⟨32094137620002403700464585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42792183493336538267286113 32094137620002403700464585)
        ·
          refine ⟨24070603215001802775348439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32094137620002403700464585 24070603215001802775348439)
          ·
            refine ⟨36105904822502704163022659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24070603215001802775348439 36105904822502704163022659)
            ·
              refine ⟨54158857233754056244533989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36105904822502704163022659 54158857233754056244533989)
              ·
                refine ⟨10154785731328885545850123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54158857233754056244533989 10154785731328885545850123)
                ·
                  refine ⟨15232178596993328318775185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10154785731328885545850123 15232178596993328318775185)
                  ·
                    refine ⟨11424133947744996239081389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15232178596993328318775185 11424133947744996239081389)
                    ·
                      refine ⟨4284050230404373589655521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11424133947744996239081389 4284050230404373589655521)
                      ·
                        rfl

theorem cell23_8343158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_8343158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343158 prefixEnd_8343158 := by exact prefixLift 8343158
  have htrace : WordTrace (prefixWord ++ tailWord_8343158) baseStart_8343158 baseEnd_8343158 := by
    simpa [prefixWord, tailWord_8343158, baseEnd_8343158] using wordTrace_append hprefix tailTrace_8343158
  have hstable : (prefixWord ++ tailWord_8343158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343158).length < 2 ^ (prefixWord ++ tailWord_8343158).sum := by decide
  have hdescent : baseEnd_8343158 < baseStart_8343158 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343228 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 1, 4, 2]
def baseStart_8343228 : Nat := 118140960795 + 8343228 * 2 ^ 59
def prefixEnd_8343228 : Nat := 4983230072969 + 3 ^ 40 * 8343228 * 2
def baseEnd_8343228 : Nat := 4284086174050188315780199

theorem tailTrace_8343228 : CollatzResearch.WordTrace tailWord_8343228 prefixEnd_8343228 4284086174050188315780199 := by
  unfold tailWord_8343228
  simp only [CollatzResearch.WordTrace]
  refine ⟨152151262308958670372319169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202868349745278227163092225 152151262308958670372319169)
  ·
    refine ⟨114113446731719002779239377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152151262308958670372319169 114113446731719002779239377)
    ·
      refine ⟨85585085048789252084429533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114113446731719002779239377 85585085048789252084429533)
      ·
        refine ⟨32094406893295969531661075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85585085048789252084429533 32094406893295969531661075)
        ·
          refine ⟨48141610339943954297491613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32094406893295969531661075 48141610339943954297491613)
          ·
            refine ⟨18053103877478982861559355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48141610339943954297491613 18053103877478982861559355)
            ·
              refine ⟨27079655816218474292339033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18053103877478982861559355 27079655816218474292339033)
              ·
                refine ⟨20309741862163855719254275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27079655816218474292339033 20309741862163855719254275)
                ·
                  refine ⟨30464612793245783578881413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20309741862163855719254275 30464612793245783578881413)
                  ·
                    refine ⟨5712114898733584421040265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30464612793245783578881413 5712114898733584421040265)
                    ·
                      refine ⟨4284086174050188315780199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5712114898733584421040265 4284086174050188315780199)
                      ·
                        rfl

theorem cell23_8343228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_8343228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343228 prefixEnd_8343228 := by exact prefixLift 8343228
  have htrace : WordTrace (prefixWord ++ tailWord_8343228) baseStart_8343228 baseEnd_8343228 := by
    simpa [prefixWord, tailWord_8343228, baseEnd_8343228] using wordTrace_append hprefix tailTrace_8343228
  have hstable : (prefixWord ++ tailWord_8343228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343228).length < 2 ^ (prefixWord ++ tailWord_8343228).sum := by decide
  have hdescent : baseEnd_8343228 < baseStart_8343228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343264 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 4, 5]
def baseStart_8343264 : Nat := 118140960795 + 8343264 * 2 ^ 59
def prefixEnd_8343264 : Nat := 4983230072969 + 3 ^ 40 * 8343264 * 2
def baseEnd_8343264 : Nat := 1428034886451250058310011

theorem tailTrace_8343264 : CollatzResearch.WordTrace tailWord_8343264 prefixEnd_8343264 1428034886451250058310011 := by
  unfold tailWord_8343264
  simp only [CollatzResearch.WordTrace]
  refine ⟨152151918822893459446474423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202869225097191279261965897 152151918822893459446474423)
  ·
    refine ⟨228227878234340189169711635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152151918822893459446474423 228227878234340189169711635)
    ·
      refine ⟨342341817351510283754567453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228227878234340189169711635 342341817351510283754567453)
      ·
        refine ⟨128378181506816356407962795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342341817351510283754567453 128378181506816356407962795)
        ·
          refine ⟨192567272260224534611944193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128378181506816356407962795 192567272260224534611944193)
          ·
            refine ⟨144425454195168400958958145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192567272260224534611944193 144425454195168400958958145)
            ·
              refine ⟨108319090646376300719218609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144425454195168400958958145 108319090646376300719218609)
              ·
                refine ⟨81239317984782225539413957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108319090646376300719218609 81239317984782225539413957)
                ·
                  refine ⟨15232372122146667288640117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81239317984782225539413957 15232372122146667288640117)
                  ·
                    refine ⟨1428034886451250058310011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15232372122146667288640117 1428034886451250058310011)
                    ·
                      rfl

theorem cell23_8343264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4, 5].length) (baseStart_8343264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343264 prefixEnd_8343264 := by exact prefixLift 8343264
  have htrace : WordTrace (prefixWord ++ tailWord_8343264) baseStart_8343264 baseEnd_8343264 := by
    simpa [prefixWord, tailWord_8343264, baseEnd_8343264] using wordTrace_append hprefix tailTrace_8343264
  have hstable : (prefixWord ++ tailWord_8343264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343264).length < 2 ^ (prefixWord ++ tailWord_8343264).sum := by decide
  have hdescent : baseEnd_8343264 < baseStart_8343264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343274 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_8343274 : Nat := 118140960795 + 8343274 * 2 ^ 59
def prefixEnd_8343274 : Nat := 4983230072969 + 3 ^ 40 * 8343274 * 2
def baseEnd_8343274 : Nat := 4284109794160295135804987

theorem tailTrace_8343274 : CollatzResearch.WordTrace tailWord_8343274 prefixEnd_8343274 4284109794160295135804987 := by
  unfold tailWord_8343274
  simp only [CollatzResearch.WordTrace]
  refine ⟨76076050593937672650203219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202869468250500460400541917 76076050593937672650203219)
  ·
    refine ⟨114114075890906508975304829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76076050593937672650203219 114114075890906508975304829)
    ·
      refine ⟨42792778459089940865739311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114114075890906508975304829 42792778459089940865739311)
      ·
        refine ⟨64189167688634911298608967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42792778459089940865739311 64189167688634911298608967)
        ·
          refine ⟨96283751532952366947913451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64189167688634911298608967 96283751532952366947913451)
          ·
            refine ⟨144425627299428550421870177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96283751532952366947913451 144425627299428550421870177)
            ·
              refine ⟨108319220474571412816402633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144425627299428550421870177 108319220474571412816402633)
              ·
                refine ⟨81239415355928559612301975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108319220474571412816402633 81239415355928559612301975)
                ·
                  refine ⟨121859123033892839418452963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81239415355928559612301975 121859123033892839418452963)
                  ·
                    refine ⟨182788684550839259127679445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121859123033892839418452963 182788684550839259127679445)
                    ·
                      refine ⟨4284109794160295135804987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182788684550839259127679445 4284109794160295135804987)
                      ·
                        rfl

theorem cell23_8343274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_8343274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343274 prefixEnd_8343274 := by exact prefixLift 8343274
  have htrace : WordTrace (prefixWord ++ tailWord_8343274) baseStart_8343274 baseEnd_8343274 := by
    simpa [prefixWord, tailWord_8343274, baseEnd_8343274] using wordTrace_append hprefix tailTrace_8343274
  have hstable : (prefixWord ++ tailWord_8343274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343274).length < 2 ^ (prefixWord ++ tailWord_8343274).sum := by decide
  have hdescent : baseEnd_8343274 < baseStart_8343274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343281 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 2, 5]
def baseStart_8343281 : Nat := 118140960795 + 8343281 * 2 ^ 59
def prefixEnd_8343281 : Nat := 4983230072969 + 3 ^ 40 * 8343281 * 2
def baseEnd_8343281 : Nat := 1428037796174958869472485

theorem tailTrace_8343281 : CollatzResearch.WordTrace tailWord_8343281 prefixEnd_8343281 1428037796174958869472485 := by
  unfold tailWord_8343281
  simp only [CollatzResearch.WordTrace]
  refine ⟨304304457686725330796317697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202869638457816887197545131 304304457686725330796317697)
  ·
    refine ⟨228228343265043998097238273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304304457686725330796317697 228228343265043998097238273)
    ·
      refine ⟨171171257448782998572928705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228228343265043998097238273 171171257448782998572928705)
      ·
        refine ⟨128378443086587248929696529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171171257448782998572928705 128378443086587248929696529)
        ·
          refine ⟨96283832314940436697272397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128378443086587248929696529 96283832314940436697272397)
          ·
            refine ⟨36106437118102663761477149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96283832314940436697272397 36106437118102663761477149)
            ·
              refine ⟨13539913919288498910553931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36106437118102663761477149 13539913919288498910553931)
              ·
                refine ⟨20309870878932748365830897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13539913919288498910553931 20309870878932748365830897)
                ·
                  refine ⟨15232403159199561274373173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20309870878932748365830897 15232403159199561274373173)
                  ·
                    refine ⟨1428037796174958869472485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15232403159199561274373173 1428037796174958869472485)
                    ·
                      rfl

theorem cell23_8343281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_8343281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343281 prefixEnd_8343281 := by exact prefixLift 8343281
  have htrace : WordTrace (prefixWord ++ tailWord_8343281) baseStart_8343281 baseEnd_8343281 := by
    simpa [prefixWord, tailWord_8343281, baseEnd_8343281] using wordTrace_append hprefix tailTrace_8343281
  have hstable : (prefixWord ++ tailWord_8343281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343281).length < 2 ^ (prefixWord ++ tailWord_8343281).sum := by decide
  have hdescent : baseEnd_8343281 < baseStart_8343281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343345 : List Nat := [1, 2, 2, 3, 2, 2, 3, 3, 1, 4]
def baseStart_8343345 : Nat := 118140960795 + 8343345 * 2 ^ 59
def prefixEnd_8343345 : Nat := 4983230072969 + 3 ^ 40 * 8343345 * 2
def baseEnd_8343345 : Nat := 1428048750428921452672387

theorem tailTrace_8343345 : CollatzResearch.WordTrace tailWord_8343345 prefixEnd_8343345 1428048750428921452672387 := by
  unfold tailWord_8343345
  simp only [CollatzResearch.WordTrace]
  refine ⟨304306791958493469726647489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202871194638995646484431659 304306791958493469726647489)
  ·
    refine ⟨228230093968870102294985617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304306791958493469726647489 228230093968870102294985617)
    ·
      refine ⟨171172570476652576721239213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228230093968870102294985617 171172570476652576721239213)
      ·
        refine ⟨64189713928744716270464705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171172570476652576721239213 64189713928744716270464705)
        ·
          refine ⟨48142285446558537202848529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64189713928744716270464705 48142285446558537202848529)
          ·
            refine ⟨36106714084918902902136397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48142285446558537202848529 36106714084918902902136397)
            ·
              refine ⟨13540017781844588588301149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36106714084918902902136397 13540017781844588588301149)
              ·
                refine ⟨5077506668191720720612931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13540017781844588588301149 5077506668191720720612931)
                ·
                  refine ⟨7616260002287581080919397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077506668191720720612931 7616260002287581080919397)
                  ·
                    refine ⟨1428048750428921452672387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7616260002287581080919397 1428048750428921452672387)
                    ·
                      rfl

theorem cell23_8343345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_8343345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343345 prefixEnd_8343345 := by exact prefixLift 8343345
  have htrace : WordTrace (prefixWord ++ tailWord_8343345) baseStart_8343345 baseEnd_8343345 := by
    simpa [prefixWord, tailWord_8343345, baseEnd_8343345] using wordTrace_append hprefix tailTrace_8343345
  have hstable : (prefixWord ++ tailWord_8343345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343345).length < 2 ^ (prefixWord ++ tailWord_8343345).sum := by decide
  have hdescent : baseEnd_8343345 < baseStart_8343345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343401 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 6, 4]
def baseStart_8343401 : Nat := 118140960795 + 8343401 * 2 ^ 59
def prefixEnd_8343401 : Nat := 4983230072969 + 3 ^ 40 * 8343401 * 2
def baseEnd_8343401 : Nat := 1428058335401138712972301

theorem tailTrace_8343401 : CollatzResearch.WordTrace tailWord_8343401 prefixEnd_8343401 1428058335401138712972301 := by
  unfold tailWord_8343401
  simp only [CollatzResearch.WordTrace]
  refine ⟨304308834446290591290686057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202872556297527060860457371 304308834446290591290686057)
  ·
    refine ⟨228231625834717943468014543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304308834446290591290686057 228231625834717943468014543)
    ·
      refine ⟨342347438752076915202021815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228231625834717943468014543 342347438752076915202021815)
      ·
        refine ⟨513521158128115372803032723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342347438752076915202021815 513521158128115372803032723)
        ·
          refine ⟨770281737192173059204549085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513521158128115372803032723 770281737192173059204549085)
          ·
            refine ⟨288855651447064897201705907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 770281737192173059204549085 288855651447064897201705907)
            ·
              refine ⟨433283477170597345802558861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288855651447064897201705907 433283477170597345802558861)
              ·
                refine ⟨162481303938974004675959573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433283477170597345802558861 162481303938974004675959573)
                ·
                  refine ⟨7616311122139406469185605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162481303938974004675959573 7616311122139406469185605)
                  ·
                    refine ⟨1428058335401138712972301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7616311122139406469185605 1428058335401138712972301)
                    ·
                      rfl

theorem cell23_8343401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 4].length) (baseStart_8343401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343401 prefixEnd_8343401 := by exact prefixLift 8343401
  have htrace : WordTrace (prefixWord ++ tailWord_8343401) baseStart_8343401 baseEnd_8343401 := by
    simpa [prefixWord, tailWord_8343401, baseEnd_8343401] using wordTrace_append hprefix tailTrace_8343401
  have hstable : (prefixWord ++ tailWord_8343401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343401).length < 2 ^ (prefixWord ++ tailWord_8343401).sum := by decide
  have hdescent : baseEnd_8343401 < baseStart_8343401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343418 : List Nat := [3, 1, 1, 1, 1, 1, 5, 4, 2, 4]
def baseStart_8343418 : Nat := 118140960795 + 8343418 * 2 ^ 59
def prefixEnd_8343418 : Nat := 4983230072969 + 3 ^ 40 * 8343418 * 2
def baseEnd_8343418 : Nat := 1428061245124847524134775

theorem tailTrace_8343418 : CollatzResearch.WordTrace tailWord_8343418 prefixEnd_8343418 1428061245124847524134775 := by
  unfold tailWord_8343418
  simp only [CollatzResearch.WordTrace]
  refine ⟨76077363621807250798513727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202872969658152668796036605 76077363621807250798513727)
  ·
    refine ⟨114116045432710876197770591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76077363621807250798513727 114116045432710876197770591)
    ·
      refine ⟨171174068149066314296655887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114116045432710876197770591 171174068149066314296655887)
      ·
        refine ⟨256761102223599471444983831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171174068149066314296655887 256761102223599471444983831)
        ·
          refine ⟨385141653335399207167475747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256761102223599471444983831 385141653335399207167475747)
          ·
            refine ⟨577712480003098810751213621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385141653335399207167475747 577712480003098810751213621)
            ·
              refine ⟨54160545000290513507926277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 577712480003098810751213621 54160545000290513507926277)
              ·
                refine ⟨10155102187554471282736177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54160545000290513507926277 10155102187554471282736177)
                ·
                  refine ⟨7616326640665853462052133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10155102187554471282736177 7616326640665853462052133)
                  ·
                    refine ⟨1428061245124847524134775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7616326640665853462052133 1428061245124847524134775)
                    ·
                      rfl

theorem cell23_8343418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_8343418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343418 prefixEnd_8343418 := by exact prefixLift 8343418
  have htrace : WordTrace (prefixWord ++ tailWord_8343418) baseStart_8343418 baseEnd_8343418 := by
    simpa [prefixWord, tailWord_8343418, baseEnd_8343418] using wordTrace_append hprefix tailTrace_8343418
  have hstable : (prefixWord ++ tailWord_8343418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343418).length < 2 ^ (prefixWord ++ tailWord_8343418).sum := by decide
  have hdescent : baseEnd_8343418 < baseStart_8343418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343421 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_8343421 : Nat := 118140960795 + 8343421 * 2 ^ 59
def prefixEnd_8343421 : Nat := 4983230072969 + 3 ^ 40 * 8343421 * 2
def baseEnd_8343421 : Nat := 4284185275816506060666811

theorem tailTrace_8343421 : CollatzResearch.WordTrace tailWord_8343421 prefixEnd_8343421 4284185275816506060666811 := by
  unfold tailWord_8343421
  simp only [CollatzResearch.WordTrace]
  refine ⟨304309563906218134706414117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202873042604145423137609411 304309563906218134706414117)
  ·
    refine ⟨57058043232415900257452647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304309563906218134706414117 57058043232415900257452647)
    ·
      refine ⟨85587064848623850386178971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57058043232415900257452647 85587064848623850386178971)
      ·
        refine ⟨128380597272935775579268457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85587064848623850386178971 128380597272935775579268457)
        ·
          refine ⟨96285447954701831684451343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128380597272935775579268457 96285447954701831684451343)
          ·
            refine ⟨144428171932052747526677015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96285447954701831684451343 144428171932052747526677015)
            ·
              refine ⟨216642257898079121290015523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144428171932052747526677015 216642257898079121290015523)
              ·
                refine ⟨324963386847118681935023285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216642257898079121290015523 324963386847118681935023285)
                ·
                  refine ⟨30465317516917376431408433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 324963386847118681935023285 30465317516917376431408433)
                  ·
                    refine ⟨22848988137688032323556325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30465317516917376431408433 22848988137688032323556325)
                    ·
                      refine ⟨4284185275816506060666811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22848988137688032323556325 4284185275816506060666811)
                      ·
                        rfl

theorem cell23_8343421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_8343421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343421 prefixEnd_8343421 := by exact prefixLift 8343421
  have htrace : WordTrace (prefixWord ++ tailWord_8343421) baseStart_8343421 baseEnd_8343421 := by
    simpa [prefixWord, tailWord_8343421, baseEnd_8343421] using wordTrace_append hprefix tailTrace_8343421
  have hstable : (prefixWord ++ tailWord_8343421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343421).length < 2 ^ (prefixWord ++ tailWord_8343421).sum := by decide
  have hdescent : baseEnd_8343421 < baseStart_8343421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343428 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_8343428 : Nat := 118140960795 + 8343428 * 2 ^ 59
def prefixEnd_8343428 : Nat := 4983230072969 + 3 ^ 40 * 8343428 * 2
def baseEnd_8343428 : Nat := 4284188870181087533279279

theorem tailTrace_8343428 : CollatzResearch.WordTrace tailWord_8343428 prefixEnd_8343428 4284188870181087533279279 := by
  unfold tailWord_8343428
  simp only [CollatzResearch.WordTrace]
  refine ⟨152154909608596387450959469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202873212811461849934612625 152154909608596387450959469)
  ·
    refine ⟨57058091103223645294109801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152154909608596387450959469 57058091103223645294109801)
    ·
      refine ⟨42793568327417733970582351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57058091103223645294109801 42793568327417733970582351)
      ·
        refine ⟨64190352491126600955873527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42793568327417733970582351 64190352491126600955873527)
        ·
          refine ⟨96285528736689901433810291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64190352491126600955873527 96285528736689901433810291)
          ·
            refine ⟨144428293105034852150715437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96285528736689901433810291 144428293105034852150715437)
            ·
              refine ⟨54160609914388069556518289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144428293105034852150715437 54160609914388069556518289)
              ·
                refine ⟨40620457435791052167388717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54160609914388069556518289 40620457435791052167388717)
                ·
                  refine ⟨15232671538421644562770769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40620457435791052167388717 15232671538421644562770769)
                  ·
                    refine ⟨11424503653816233422078077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15232671538421644562770769 11424503653816233422078077)
                    ·
                      refine ⟨4284188870181087533279279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11424503653816233422078077 4284188870181087533279279)
                      ·
                        rfl

theorem cell23_8343428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_8343428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343428 prefixEnd_8343428 := by exact prefixLift 8343428
  have htrace : WordTrace (prefixWord ++ tailWord_8343428) baseStart_8343428 baseEnd_8343428 := by
    simpa [prefixWord, tailWord_8343428, baseEnd_8343428] using wordTrace_append hprefix tailTrace_8343428
  have hstable : (prefixWord ++ tailWord_8343428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343428).length < 2 ^ (prefixWord ++ tailWord_8343428).sum := by decide
  have hdescent : baseEnd_8343428 < baseStart_8343428 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343442 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_8343442 : Nat := 118140960795 + 8343442 * 2 ^ 59
def prefixEnd_8343442 : Nat := 4983230072969 + 3 ^ 40 * 8343442 * 2
def baseEnd_8343442 : Nat := 4284196058910250478504215

theorem tailTrace_8343442 : CollatzResearch.WordTrace tailWord_8343442 prefixEnd_8343442 4284196058910250478504215 := by
  unfold tailWord_8343442
  simp only [CollatzResearch.WordTrace]
  refine ⟨76077582459785513823232145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202873553226094703528619053 76077582459785513823232145)
  ·
    refine ⟨57058186844839135367424109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76077582459785513823232145 57058186844839135367424109)
    ·
      refine ⟨21396820066814675762784041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57058186844839135367424109 21396820066814675762784041)
      ·
        refine ⟨16047615050111006822088031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21396820066814675762784041 16047615050111006822088031)
        ·
          refine ⟨24071422575166510233132047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16047615050111006822088031 24071422575166510233132047)
          ·
            refine ⟨36107133862749765349698071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24071422575166510233132047 36107133862749765349698071)
            ·
              refine ⟨54160700794124648024547107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36107133862749765349698071 54160700794124648024547107)
              ·
                refine ⟨81241051191186972036820661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54160700794124648024547107 81241051191186972036820661)
                ·
                  refine ⟨7616348549173778628451937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81241051191186972036820661 7616348549173778628451937)
                  ·
                    refine ⟨5712261411880333971338953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7616348549173778628451937 5712261411880333971338953)
                    ·
                      refine ⟨4284196058910250478504215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5712261411880333971338953 4284196058910250478504215)
                      ·
                        rfl

theorem cell23_8343442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_8343442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343442 prefixEnd_8343442 := by exact prefixLift 8343442
  have htrace : WordTrace (prefixWord ++ tailWord_8343442) baseStart_8343442 baseEnd_8343442 := by
    simpa [prefixWord, tailWord_8343442, baseEnd_8343442] using wordTrace_append hprefix tailTrace_8343442
  have hstable : (prefixWord ++ tailWord_8343442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343442).length < 2 ^ (prefixWord ++ tailWord_8343442).sum := by decide
  have hdescent : baseEnd_8343442 < baseStart_8343442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343476 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_8343476 : Nat := 118140960795 + 8343476 * 2 ^ 59
def prefixEnd_8343476 : Nat := 4983230072969 + 3 ^ 40 * 8343476 * 2
def baseEnd_8343476 : Nat := 4284213517252503345479059

theorem tailTrace_8343476 : CollatzResearch.WordTrace tailWord_8343476 prefixEnd_8343476 4284213517252503345479059 := by
  unfold tailWord_8343476
  simp only [CollatzResearch.WordTrace]
  refine ⟨152155784960509439549833141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202874379947345919399777521 152155784960509439549833141)
  ·
    refine ⟨14264604840047759957796857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152155784960509439549833141 14264604840047759957796857)
    ·
      refine ⟨10698453630035819968347643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14264604840047759957796857 10698453630035819968347643)
      ·
        refine ⟨16047680445053729952521465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10698453630035819968347643 16047680445053729952521465)
        ·
          refine ⟨12035760333790297464391099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16047680445053729952521465 12035760333790297464391099)
          ·
            refine ⟨18053640500685446196586649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12035760333790297464391099 18053640500685446196586649)
            ·
              refine ⟨13540230375514084647439987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18053640500685446196586649 13540230375514084647439987)
              ·
                refine ⟨20310345563271126971159981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13540230375514084647439987 20310345563271126971159981)
                ·
                  refine ⟨7616379586226672614184993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20310345563271126971159981 7616379586226672614184993)
                  ·
                    refine ⟨5712284689670004460638745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7616379586226672614184993 5712284689670004460638745)
                    ·
                      refine ⟨4284213517252503345479059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5712284689670004460638745 4284213517252503345479059)
                      ·
                        rfl

theorem cell23_8343476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_8343476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343476 prefixEnd_8343476 := by exact prefixLift 8343476
  have htrace : WordTrace (prefixWord ++ tailWord_8343476) baseStart_8343476 baseEnd_8343476 := by
    simpa [prefixWord, tailWord_8343476, baseEnd_8343476] using wordTrace_append hprefix tailTrace_8343476
  have hstable : (prefixWord ++ tailWord_8343476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343476).length < 2 ^ (prefixWord ++ tailWord_8343476).sum := by decide
  have hdescent : baseEnd_8343476 < baseStart_8343476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343502 : List Nat := [4, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2]
def baseStart_8343502 : Nat := 118140960795 + 8343502 * 2 ^ 59
def prefixEnd_8343502 : Nat := 4983230072969 + 3 ^ 40 * 8343502 * 2
def baseEnd_8343502 : Nat := 4284226867749520243753939

theorem tailTrace_8343502 : CollatzResearch.WordTrace tailWord_8343502 prefixEnd_8343502 4284226867749520243753939 := by
  unfold tailWord_8343502
  simp only [CollatzResearch.WordTrace]
  refine ⟨38039064777365585692514095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202875012145949790360075173 38039064777365585692514095)
  ·
    refine ⟨57058597166048378538771143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38039064777365585692514095 57058597166048378538771143)
    ·
      refine ⟨85587895749072567808156715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57058597166048378538771143 85587895749072567808156715)
      ·
        refine ⟨128381843623608851712235073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85587895749072567808156715 128381843623608851712235073)
        ·
          refine ⟨96286382717706638784176305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128381843623608851712235073 96286382717706638784176305)
          ·
            refine ⟨72214787038279979088132229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96286382717706638784176305 72214787038279979088132229)
            ·
              refine ⟨13540272569677496079024793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72214787038279979088132229 13540272569677496079024793)
              ·
                refine ⟨10155204427258122059268595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13540272569677496079024793 10155204427258122059268595)
                ·
                  refine ⟨15232806640887183088902893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10155204427258122059268595 15232806640887183088902893)
                  ·
                    refine ⟨5712302490332693658338585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15232806640887183088902893 5712302490332693658338585)
                    ·
                      refine ⟨4284226867749520243753939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5712302490332693658338585 4284226867749520243753939)
                      ·
                        rfl

theorem cell23_8343502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_8343502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343502 prefixEnd_8343502 := by exact prefixLift 8343502
  have htrace : WordTrace (prefixWord ++ tailWord_8343502) baseStart_8343502 baseEnd_8343502 := by
    simpa [prefixWord, tailWord_8343502, baseEnd_8343502] using wordTrace_append hprefix tailTrace_8343502
  have hstable : (prefixWord ++ tailWord_8343502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343502).length < 2 ^ (prefixWord ++ tailWord_8343502).sum := by decide
  have hdescent : baseEnd_8343502 < baseStart_8343502 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343510 : List Nat := [5, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_8343510 : Nat := 118140960795 + 8343510 * 2 ^ 59
def prefixEnd_8343510 : Nat := 4983230072969 + 3 ^ 40 * 8343510 * 2
def baseEnd_8343510 : Nat := 4284230975594756212453903

theorem tailTrace_8343510 : CollatzResearch.WordTrace tailWord_8343510 prefixEnd_8343510 4284230975594756212453903 := by
  unfold tailWord_8343510
  simp only [CollatzResearch.WordTrace]
  refine ⟨19019550625180981431650249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202875206668597135270935989 19019550625180981431650249)
  ·
    refine ⟨14264662968885736073737687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19019550625180981431650249 14264662968885736073737687)
    ·
      refine ⟨21396994453328604110606531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14264662968885736073737687 21396994453328604110606531)
      ·
        refine ⟨32095491679992906165909797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21396994453328604110606531 32095491679992906165909797)
        ·
          refine ⟨6017904689998669906108087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32095491679992906165909797 6017904689998669906108087)
          ·
            refine ⟨9026857034998004859162131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017904689998669906108087 9026857034998004859162131)
            ·
              refine ⟨13540285552497007288743197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9026857034998004859162131 13540285552497007288743197)
              ·
                refine ⟨5077607082186377733278699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13540285552497007288743197 5077607082186377733278699)
                ·
                  refine ⟨7616410623279566599918049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077607082186377733278699 7616410623279566599918049)
                  ·
                    refine ⟨5712307967459674949938537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7616410623279566599918049 5712307967459674949938537)
                    ·
                      refine ⟨4284230975594756212453903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5712307967459674949938537 4284230975594756212453903)
                      ·
                        rfl

theorem cell23_8343510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_8343510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343510 prefixEnd_8343510 := by exact prefixLift 8343510
  have htrace : WordTrace (prefixWord ++ tailWord_8343510) baseStart_8343510 baseEnd_8343510 := by
    simpa [prefixWord, tailWord_8343510, baseEnd_8343510] using wordTrace_append hprefix tailTrace_8343510
  have hstable : (prefixWord ++ tailWord_8343510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343510).length < 2 ^ (prefixWord ++ tailWord_8343510).sum := by decide
  have hdescent : baseEnd_8343510 < baseStart_8343510 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343521 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 9]
def baseStart_8343521 : Nat := 118140960795 + 8343521 * 2 ^ 59
def prefixEnd_8343521 : Nat := 4983230072969 + 3 ^ 40 * 8343521 * 2
def baseEnd_8343521 : Nat := 476026291542439518824039

theorem tailTrace_8343521 : CollatzResearch.WordTrace tailWord_8343521 prefixEnd_8343521 476026291542439518824039 := by
  unfold tailWord_8343521
  simp only [CollatzResearch.WordTrace]
  refine ⟨304313211205855851785054417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202875474137237234523369611 304313211205855851785054417)
  ·
    refine ⟨228234908404391888838790813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304313211205855851785054417 228234908404391888838790813)
    ·
      refine ⟨85588090651646958314546555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228234908404391888838790813 85588090651646958314546555)
      ·
        refine ⟨128382135977470437471819833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85588090651646958314546555 128382135977470437471819833)
        ·
          refine ⟨96286601983102828103864875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128382135977470437471819833 96286601983102828103864875)
          ·
            refine ⟨144429902974654242155797313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96286601983102828103864875 144429902974654242155797313)
            ·
              refine ⟨108322427230990681616847985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144429902974654242155797313 108322427230990681616847985)
              ·
                refine ⟨81241820423243011212635989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108322427230990681616847985 81241820423243011212635989)
                ·
                  refine ⟨476026291542439518824039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81241820423243011212635989 476026291542439518824039)
                  ·
                    rfl

theorem cell23_8343521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 9].length) (baseStart_8343521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343521 prefixEnd_8343521 := by exact prefixLift 8343521
  have htrace : WordTrace (prefixWord ++ tailWord_8343521) baseStart_8343521 baseEnd_8343521 := by
    simpa [prefixWord, tailWord_8343521, baseEnd_8343521] using wordTrace_append hprefix tailTrace_8343521
  have hstable : (prefixWord ++ tailWord_8343521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343521).length < 2 ^ (prefixWord ++ tailWord_8343521).sum := by decide
  have hdescent : baseEnd_8343521 < baseStart_8343521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343548 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_8343548 : Nat := 118140960795 + 8343548 * 2 ^ 59
def prefixEnd_8343548 : Nat := 4983230072969 + 3 ^ 40 * 8343548 * 2
def baseEnd_8343548 : Nat := 4284250487859627063778727

theorem tailTrace_8343548 : CollatzResearch.WordTrace tailWord_8343548 prefixEnd_8343548 4284250487859627063778727 := by
  unfold tailWord_8343548
  simp only [CollatzResearch.WordTrace]
  refine ⟨152157097988379017698143649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202876130651172023597524865 152157097988379017698143649)
  ·
    refine ⟨114117823491284263273607737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152157097988379017698143649 114117823491284263273607737)
    ·
      refine ⟨85588367618463197455205803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114117823491284263273607737 85588367618463197455205803)
      ·
        refine ⟨128382551427694796182808705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85588367618463197455205803 128382551427694796182808705)
        ·
          refine ⟨96286913570771097137106529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128382551427694796182808705 96286913570771097137106529)
          ·
            refine ⟨72215185178078322852829897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96286913570771097137106529 72215185178078322852829897)
            ·
              refine ⟨54161388883558742139622423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72215185178078322852829897 54161388883558742139622423)
              ·
                refine ⟨81242083325338113209433635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54161388883558742139622423 81242083325338113209433635)
                ·
                  refine ⟨121863124988007169814150453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81242083325338113209433635 121863124988007169814150453)
                  ·
                    refine ⟨11424667967625672170076605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121863124988007169814150453 11424667967625672170076605)
                    ·
                      refine ⟨4284250487859627063778727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11424667967625672170076605 4284250487859627063778727)
                      ·
                        rfl

theorem cell23_8343548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_8343548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343548 prefixEnd_8343548 := by exact prefixLift 8343548
  have htrace : WordTrace (prefixWord ++ tailWord_8343548) baseStart_8343548 baseEnd_8343548 := by
    simpa [prefixWord, tailWord_8343548, baseEnd_8343548] using wordTrace_append hprefix tailTrace_8343548
  have hstable : (prefixWord ++ tailWord_8343548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343548).length < 2 ^ (prefixWord ++ tailWord_8343548).sum := by decide
  have hdescent : baseEnd_8343548 < baseStart_8343548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343549 : List Nat := [1, 4, 1, 1, 1, 2, 6, 1, 2, 2, 2]
def baseStart_8343549 : Nat := 118140960795 + 8343549 * 2 ^ 59
def prefixEnd_8343549 : Nat := 4983230072969 + 3 ^ 40 * 8343549 * 2
def baseEnd_8343549 : Nat := 4284251001340281559866223

theorem tailTrace_8343549 : CollatzResearch.WordTrace tailWord_8343549 prefixEnd_8343549 4284251001340281559866223 := by
  unfold tailWord_8343549
  simp only [CollatzResearch.WordTrace]
  refine ⟨304314232449754412567073701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202876154966502941711382467 304314232449754412567073701)
  ·
    refine ⟨57058918584328952356326319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304314232449754412567073701 57058918584328952356326319)
    ·
      refine ⟨85588377876493428534489479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57058918584328952356326319 85588377876493428534489479)
      ·
        refine ⟨128382566814740142801734219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85588377876493428534489479 128382566814740142801734219)
        ·
          refine ⟨192573850222110214202601329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128382566814740142801734219 192573850222110214202601329)
          ·
            refine ⟨144430387666582660651950997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192573850222110214202601329 144430387666582660651950997)
            ·
              refine ⟨6770174421871062218060203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144430387666582660651950997 6770174421871062218060203)
              ·
                refine ⟨10155261632806593327090305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6770174421871062218060203 10155261632806593327090305)
                ·
                  refine ⟨7616446224604944995317729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10155261632806593327090305 7616446224604944995317729)
                  ·
                    refine ⟨5712334668453708746488297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7616446224604944995317729 5712334668453708746488297)
                    ·
                      refine ⟨4284251001340281559866223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5712334668453708746488297 4284251001340281559866223)
                      ·
                        rfl

theorem cell23_8343549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_8343549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343549 prefixEnd_8343549 := by exact prefixLift 8343549
  have htrace : WordTrace (prefixWord ++ tailWord_8343549) baseStart_8343549 baseEnd_8343549 := by
    simpa [prefixWord, tailWord_8343549, baseEnd_8343549] using wordTrace_append hprefix tailTrace_8343549
  have hstable : (prefixWord ++ tailWord_8343549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343549).length < 2 ^ (prefixWord ++ tailWord_8343549).sum := by decide
  have hdescent : baseEnd_8343549 < baseStart_8343549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343551 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 3, 7]
def baseStart_8343551 : Nat := 118140960795 + 8343551 * 2 ^ 59
def prefixEnd_8343551 : Nat := 4983230072969 + 3 ^ 40 * 8343551 * 2
def baseEnd_8343551 : Nat := 1428084009433863517347071

theorem tailTrace_8343551 : CollatzResearch.WordTrace tailWord_8343551 prefixEnd_8343551 1428084009433863517347071 := by
  unfold tailWord_8343551
  simp only [CollatzResearch.WordTrace]
  refine ⟨304314305395747166908646507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202876203597164777939097671 304314305395747166908646507)
  ·
    refine ⟨456471458093620750362969761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304314305395747166908646507 456471458093620750362969761)
    ·
      refine ⟨342353593570215562772227321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456471458093620750362969761 342353593570215562772227321)
      ·
        refine ⟨256765195177661672079170491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342353593570215562772227321 256765195177661672079170491)
        ·
          refine ⟨385147792766492508118755737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256765195177661672079170491 385147792766492508118755737)
          ·
            refine ⟨288860844574869381089066803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385147792766492508118755737 288860844574869381089066803)
            ·
              refine ⟨433291266862304071633600205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288860844574869381089066803 433291266862304071633600205)
              ·
                refine ⟨162484225073364026862600077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433291266862304071633600205 162484225073364026862600077)
                ·
                  refine ⟨60931584402511510073475029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162484225073364026862600077 60931584402511510073475029)
                  ·
                    refine ⟨1428084009433863517347071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60931584402511510073475029 1428084009433863517347071)
                    ·
                      rfl

theorem cell23_8343551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_8343551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343551 prefixEnd_8343551 := by exact prefixLift 8343551
  have htrace : WordTrace (prefixWord ++ tailWord_8343551) baseStart_8343551 baseEnd_8343551 := by
    simpa [prefixWord, tailWord_8343551, baseEnd_8343551] using wordTrace_append hprefix tailTrace_8343551
  have hstable : (prefixWord ++ tailWord_8343551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343551).length < 2 ^ (prefixWord ++ tailWord_8343551).sum := by decide
  have hdescent : baseEnd_8343551 < baseStart_8343551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343578 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_8343578 : Nat := 118140960795 + 8343578 * 2 ^ 59
def prefixEnd_8343578 : Nat := 4983230072969 + 3 ^ 40 * 8343578 * 2
def baseEnd_8343578 : Nat := 4284265892279261946403589

theorem tailTrace_8343578 : CollatzResearch.WordTrace tailWord_8343578 prefixEnd_8343578 4284265892279261946403589 := by
  unfold tailWord_8343578
  simp only [CollatzResearch.WordTrace]
  refine ⟨76078822541662337629969847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202876860111099567013252925 76078822541662337629969847)
  ·
    refine ⟨114118233812493506444954771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76078822541662337629969847 114118233812493506444954771)
    ·
      refine ⟨171177350718740259667432157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114118233812493506444954771 171177350718740259667432157)
      ·
        refine ⟨64191506519527597375287059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171177350718740259667432157 64191506519527597375287059)
        ·
          refine ⟨96287259779291396062930589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64191506519527597375287059 96287259779291396062930589)
          ·
            refine ⟨36107722417234273523598971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96287259779291396062930589 36107722417234273523598971)
            ·
              refine ⟨54161583625851410285398457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36107722417234273523598971 54161583625851410285398457)
              ·
                refine ⟨40621187719388557714048843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54161583625851410285398457 40621187719388557714048843)
                ·
                  refine ⟨60931781579082836571073265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40621187719388557714048843 60931781579082836571073265)
                  ·
                    refine ⟨45698836184312127428304949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60931781579082836571073265 45698836184312127428304949)
                    ·
                      refine ⟨4284265892279261946403589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45698836184312127428304949 4284265892279261946403589)
                      ·
                        rfl

theorem cell23_8343578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_8343578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343578 prefixEnd_8343578 := by exact prefixLift 8343578
  have htrace : WordTrace (prefixWord ++ tailWord_8343578) baseStart_8343578 baseEnd_8343578 := by
    simpa [prefixWord, tailWord_8343578, baseEnd_8343578] using wordTrace_append hprefix tailTrace_8343578
  have hstable : (prefixWord ++ tailWord_8343578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343578).length < 2 ^ (prefixWord ++ tailWord_8343578).sum := by decide
  have hdescent : baseEnd_8343578 < baseStart_8343578 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343605 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_8343605 : Nat := 118140960795 + 8343605 * 2 ^ 59
def prefixEnd_8343605 : Nat := 4983230072969 + 3 ^ 40 * 8343605 * 2
def baseEnd_8343605 : Nat := 4284279756256933340765965

theorem tailTrace_8343605 : CollatzResearch.WordTrace tailWord_8343605 prefixEnd_8343605 4284279756256933340765965 := by
  unfold tailWord_8343605
  simp only [CollatzResearch.WordTrace]
  refine ⟨304316274937551534131112269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202877516625034356087408179 304316274937551534131112269)
  ·
    refine ⟨114118603101581825299167101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304316274937551534131112269 114118603101581825299167101)
    ·
      refine ⟨42794476163093184487187663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114118603101581825299167101 42794476163093184487187663)
      ·
        refine ⟨64191714244639776730781495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42794476163093184487187663 64191714244639776730781495)
        ·
          refine ⟨96287571366959665096172243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64191714244639776730781495 96287571366959665096172243)
          ·
            refine ⟨144431357050439497644258365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96287571366959665096172243 144431357050439497644258365)
            ·
              refine ⟨54161758893914811616596887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144431357050439497644258365 54161758893914811616596887)
              ·
                refine ⟨81242638340872217424895331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54161758893914811616596887 81242638340872217424895331)
                ·
                  refine ⟨121863957511308326137342997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81242638340872217424895331 121863957511308326137342997)
                  ·
                    refine ⟨5712373008342577787687953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121863957511308326137342997 5712373008342577787687953)
                    ·
                      refine ⟨4284279756256933340765965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5712373008342577787687953 4284279756256933340765965)
                      ·
                        rfl

theorem cell23_8343605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_8343605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343605 prefixEnd_8343605 := by exact prefixLift 8343605
  have htrace : WordTrace (prefixWord ++ tailWord_8343605) baseStart_8343605 baseEnd_8343605 := by
    simpa [prefixWord, tailWord_8343605, baseEnd_8343605] using wordTrace_append hprefix tailTrace_8343605
  have hstable : (prefixWord ++ tailWord_8343605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343605).length < 2 ^ (prefixWord ++ tailWord_8343605).sum := by decide
  have hdescent : baseEnd_8343605 < baseStart_8343605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343622 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_8343622 : Nat := 118140960795 + 8343622 * 2 ^ 59
def prefixEnd_8343622 : Nat := 4983230072969 + 3 ^ 40 * 8343622 * 2
def baseEnd_8343622 : Nat := 4284288485428059774253387

theorem tailTrace_8343622 : CollatzResearch.WordTrace tailWord_8343622 prefixEnd_8343622 4284288485428059774253387 := by
  unfold tailWord_8343622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9509902968077810813577535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202877929985659964022987413 9509902968077810813577535)
  ·
    refine ⟨14264854452116716220366303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9509902968077810813577535 14264854452116716220366303)
    ·
      refine ⟨21397281678175074330549455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14264854452116716220366303 21397281678175074330549455)
      ·
        refine ⟨32095922517262611495824183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21397281678175074330549455 32095922517262611495824183)
        ·
          refine ⟨48143883775893917243736275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32095922517262611495824183 48143883775893917243736275)
          ·
            refine ⟨72215825663840875865604413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48143883775893917243736275 72215825663840875865604413)
            ·
              refine ⟨27080934623940328449601655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72215825663840875865604413 27080934623940328449601655)
              ·
                refine ⟨40621401935910492674402483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27080934623940328449601655 40621401935910492674402483)
                ·
                  refine ⟨60932102903865739011603725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40621401935910492674402483 60932102903865739011603725)
                  ·
                    refine ⟨22849538588949652129351397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60932102903865739011603725 22849538588949652129351397)
                    ·
                      refine ⟨4284288485428059774253387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22849538588949652129351397 4284288485428059774253387)
                      ·
                        rfl

theorem cell23_8343622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_8343622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343622 prefixEnd_8343622 := by exact prefixLift 8343622
  have htrace : WordTrace (prefixWord ++ tailWord_8343622) baseStart_8343622 baseEnd_8343622 := by
    simpa [prefixWord, tailWord_8343622, baseEnd_8343622] using wordTrace_append hprefix tailTrace_8343622
  have hstable : (prefixWord ++ tailWord_8343622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343622).length < 2 ^ (prefixWord ++ tailWord_8343622).sum := by decide
  have hdescent : baseEnd_8343622 < baseStart_8343622 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343648 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 6]
def baseStart_8343648 : Nat := 118140960795 + 8343648 * 2 ^ 59
def prefixEnd_8343648 : Nat := 4983230072969 + 3 ^ 40 * 8343648 * 2
def baseEnd_8343648 : Nat := 4284301835925076672528267

theorem tailTrace_8343648 : CollatzResearch.WordTrace tailWord_8343648 prefixEnd_8343648 4284301835925076672528267 := by
  unfold tailWord_8343648
  simp only [CollatzResearch.WordTrace]
  refine ⟨152158921638197876237463799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202878562184263834983285065 152158921638197876237463799)
  ·
    refine ⟨228238382457296814356195699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152158921638197876237463799 228238382457296814356195699)
    ·
      refine ⟨342357573685945221534293549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228238382457296814356195699 342357573685945221534293549)
      ·
        refine ⟨128384090132229458075360081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342357573685945221534293549 128384090132229458075360081)
        ·
          refine ⟨96288067599172093556520061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128384090132229458075360081 96288067599172093556520061)
          ·
            refine ⟨36108025349689535083695023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96288067599172093556520061 36108025349689535083695023)
            ·
              refine ⟨54162038024534302625542535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36108025349689535083695023 54162038024534302625542535)
              ·
                refine ⟨81243057036801453938313803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54162038024534302625542535 81243057036801453938313803)
                ·
                  refine ⟨121864585555202180907470705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81243057036801453938313803 121864585555202180907470705)
                  ·
                    refine ⟨91398439166401635680603029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121864585555202180907470705 91398439166401635680603029)
                    ·
                      refine ⟨4284301835925076672528267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91398439166401635680603029 4284301835925076672528267)
                      ·
                        rfl

theorem cell23_8343648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_8343648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343648 prefixEnd_8343648 := by exact prefixLift 8343648
  have htrace : WordTrace (prefixWord ++ tailWord_8343648) baseStart_8343648 baseEnd_8343648 := by
    simpa [prefixWord, tailWord_8343648, baseEnd_8343648] using wordTrace_append hprefix tailTrace_8343648
  have hstable : (prefixWord ++ tailWord_8343648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343648).length < 2 ^ (prefixWord ++ tailWord_8343648).sum := by decide
  have hdescent : baseEnd_8343648 < baseStart_8343648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343662 : List Nat := [4, 1, 2, 2, 1, 1, 5, 1, 6]
def baseStart_8343662 : Nat := 118140960795 + 8343662 * 2 ^ 59
def prefixEnd_8343662 : Nat := 4983230072969 + 3 ^ 40 * 8343662 * 2
def baseEnd_8343662 : Nat := 476034336072693290861467

theorem tailTrace_8343662 : CollatzResearch.WordTrace tailWord_8343662 prefixEnd_8343662 476034336072693290861467 := by
  unfold tailWord_8343662
  simp only [CollatzResearch.WordTrace]
  refine ⟨38039794237293129108242155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202878902598896688577291493 38039794237293129108242155)
  ·
    refine ⟨57059691355939693662363233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38039794237293129108242155 57059691355939693662363233)
    ·
      refine ⟨42794768516954770246772425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57059691355939693662363233 42794768516954770246772425)
      ·
        refine ⟨32096076387716077685079319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42794768516954770246772425 32096076387716077685079319)
        ·
          refine ⟨48144114581574116527618979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32096076387716077685079319 48144114581574116527618979)
          ·
            refine ⟨72216171872361174791428469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48144114581574116527618979 72216171872361174791428469)
            ·
              refine ⟨6770266113033860136696419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72216171872361174791428469 6770266113033860136696419)
              ·
                refine ⟨10155399169550790205044629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6770266113033860136696419 10155399169550790205044629)
                ·
                  refine ⟨476034336072693290861467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10155399169550790205044629 476034336072693290861467)
                  ·
                    rfl

theorem cell23_8343662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_8343662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343662 prefixEnd_8343662 := by exact prefixLift 8343662
  have htrace : WordTrace (prefixWord ++ tailWord_8343662) baseStart_8343662 baseEnd_8343662 := by
    simpa [prefixWord, tailWord_8343662, baseEnd_8343662] using wordTrace_append hprefix tailTrace_8343662
  have hstable : (prefixWord ++ tailWord_8343662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343662).length < 2 ^ (prefixWord ++ tailWord_8343662).sum := by decide
  have hdescent : baseEnd_8343662 < baseStart_8343662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343665 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 3, 5, 2]
def baseStart_8343665 : Nat := 118140960795 + 8343665 * 2 ^ 59
def prefixEnd_8343665 : Nat := 4983230072969 + 3 ^ 40 * 8343665 * 2
def baseEnd_8343665 : Nat := 4284310565096203106015689

theorem tailTrace_8343665 : CollatzResearch.WordTrace tailWord_8343665 prefixEnd_8343665 4284310565096203106015689 := by
  unfold tailWord_8343665
  simp only [CollatzResearch.WordTrace]
  refine ⟨304318463317334164378296449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202878975544889442918864299 304318463317334164378296449)
  ·
    refine ⟨228238847488000623283722337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304318463317334164378296449 228238847488000623283722337)
    ·
      refine ⟨171179135616000467462791753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228238847488000623283722337 171179135616000467462791753)
      ·
        refine ⟨128384351712000350597093815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171179135616000467462791753 128384351712000350597093815)
        ·
          refine ⟨192576527568000525895640723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128384351712000350597093815 192576527568000525895640723)
          ·
            refine ⟨288864791352000788843461085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192576527568000525895640723 288864791352000788843461085)
            ·
              refine ⟨108324296757000295816297907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288864791352000788843461085 108324296757000295816297907)
              ·
                refine ⟨162486445135500443724446861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108324296757000295816297907 162486445135500443724446861)
                ·
                  refine ⟨60932416925812666396667573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162486445135500443724446861 60932416925812666396667573)
                  ·
                    refine ⟨5712414086794937474687585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60932416925812666396667573 5712414086794937474687585)
                    ·
                      refine ⟨4284310565096203106015689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5712414086794937474687585 4284310565096203106015689)
                      ·
                        rfl

theorem cell23_8343665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_8343665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343665 prefixEnd_8343665 := by exact prefixLift 8343665
  have htrace : WordTrace (prefixWord ++ tailWord_8343665) baseStart_8343665 baseEnd_8343665 := by
    simpa [prefixWord, tailWord_8343665, baseEnd_8343665] using wordTrace_append hprefix tailTrace_8343665
  have hstable : (prefixWord ++ tailWord_8343665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343665).length < 2 ^ (prefixWord ++ tailWord_8343665).sum := by decide
  have hdescent : baseEnd_8343665 < baseStart_8343665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343706 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3]
def baseStart_8343706 : Nat := 118140960795 + 8343706 * 2 ^ 59
def prefixEnd_8343706 : Nat := 4983230072969 + 3 ^ 40 * 8343706 * 2
def baseEnd_8343706 : Nat := 4284331617803037445603001

theorem tailTrace_8343706 : CollatzResearch.WordTrace tailWord_8343706 prefixEnd_8343706 4284331617803037445603001 := by
  unfold tailWord_8343706
  simp only [CollatzResearch.WordTrace]
  refine ⟨76079989677546407095134743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202879972473457085587025981 76079989677546407095134743)
  ·
    refine ⟨114119984516319610642702115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76079989677546407095134743 114119984516319610642702115)
    ·
      refine ⟨171179976774479415964053173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114119984516319610642702115 171179976774479415964053173)
      ·
        refine ⟨16048122822607445246629985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171179976774479415964053173 16048122822607445246629985)
        ·
          refine ⟨12036092116955583934972489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16048122822607445246629985 12036092116955583934972489)
          ·
            refine ⟨9027069087716687951229367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12036092116955583934972489 9027069087716687951229367)
            ·
              refine ⟨13540603631575031926844051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9027069087716687951229367 13540603631575031926844051)
              ·
                refine ⟨20310905447362547890266077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13540603631575031926844051 20310905447362547890266077)
                ·
                  refine ⟨7616589542760955458849779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20310905447362547890266077 7616589542760955458849779)
                  ·
                    refine ⟨11424884314141433188274669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7616589542760955458849779 11424884314141433188274669)
                    ·
                      refine ⟨4284331617803037445603001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11424884314141433188274669 4284331617803037445603001)
                      ·
                        rfl

theorem cell23_8343706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_8343706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343706 prefixEnd_8343706 := by exact prefixLift 8343706
  have htrace : WordTrace (prefixWord ++ tailWord_8343706) baseStart_8343706 baseEnd_8343706 := by
    simpa [prefixWord, tailWord_8343706, baseEnd_8343706] using wordTrace_append hprefix tailTrace_8343706
  have hstable : (prefixWord ++ tailWord_8343706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343706).length < 2 ^ (prefixWord ++ tailWord_8343706).sum := by decide
  have hdescent : baseEnd_8343706 < baseStart_8343706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343756 : List Nat := [2, 2, 1, 6, 1, 1, 2, 2, 2, 4]
def baseStart_8343756 : Nat := 118140960795 + 8343756 * 2 ^ 59
def prefixEnd_8343756 : Nat := 4983230072969 + 3 ^ 40 * 8343756 * 2
def baseEnd_8343756 : Nat := 1428119097278587416659257

theorem tailTrace_8343756 : CollatzResearch.WordTrace tailWord_8343756 prefixEnd_8343756 1428119097278587416659257 := by
  unfold tailWord_8343756
  simp only [CollatzResearch.WordTrace]
  refine ⟨152160891180002243459929561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202881188240002991279906081 152160891180002243459929561)
  ·
    refine ⟨114120668385001682594947171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152160891180002243459929561 114120668385001682594947171)
    ·
      refine ⟨171181002577502523892420757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114120668385001682594947171 171181002577502523892420757)
      ·
        refine ⟨8024109495820430807457223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171181002577502523892420757 8024109495820430807457223)
        ·
          refine ⟨12036164243730646211185835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8024109495820430807457223 12036164243730646211185835)
          ·
            refine ⟨18054246365595969316778753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12036164243730646211185835 18054246365595969316778753)
            ·
              refine ⟨13540684774196976987584065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18054246365595969316778753 13540684774196976987584065)
              ·
                refine ⟨10155513580647732740688049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13540684774196976987584065 10155513580647732740688049)
                ·
                  refine ⟨7616635185485799555516037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10155513580647732740688049 7616635185485799555516037)
                  ·
                    refine ⟨1428119097278587416659257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7616635185485799555516037 1428119097278587416659257)
                    ·
                      rfl

theorem cell23_8343756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_8343756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343756 prefixEnd_8343756 := by exact prefixLift 8343756
  have htrace : WordTrace (prefixWord ++ tailWord_8343756) baseStart_8343756 baseEnd_8343756 := by
    simpa [prefixWord, tailWord_8343756, baseEnd_8343756] using wordTrace_append hprefix tailTrace_8343756
  have hstable : (prefixWord ++ tailWord_8343756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343756).length < 2 ^ (prefixWord ++ tailWord_8343756).sum := by decide
  have hdescent : baseEnd_8343756 < baseStart_8343756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343805 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_8343805 : Nat := 118140960795 + 8343805 * 2 ^ 59
def prefixEnd_8343805 : Nat := 4983230072969 + 3 ^ 40 * 8343805 * 2
def baseEnd_8343805 : Nat := 4284382452387832558265045

theorem tailTrace_8343805 : CollatzResearch.WordTrace tailWord_8343805 prefixEnd_8343805 4284382452387832558265045 := by
  unfold tailWord_8343805
  simp only [CollatzResearch.WordTrace]
  refine ⟨304323569536826968288392869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202882379691217978858928579 304323569536826968288392869)
  ·
    refine ⟨57060669288155056554073663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304323569536826968288392869 57060669288155056554073663)
    ·
      refine ⟨85591003932232584831110495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57060669288155056554073663 85591003932232584831110495)
      ·
        refine ⟨128386505898348877246665743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85591003932232584831110495 128386505898348877246665743)
        ·
          refine ⟨192579758847523315869998615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128386505898348877246665743 192579758847523315869998615)
          ·
            refine ⟨288869638271284973804997923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192579758847523315869998615 288869638271284973804997923)
            ·
              refine ⟨433304457406927460707496885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288869638271284973804997923 433304457406927460707496885)
              ·
                refine ⟨40622292881899449441327833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 433304457406927460707496885 40622292881899449441327833)
                ·
                  refine ⟨30466719661424587080995875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40622292881899449441327833 30466719661424587080995875)
                  ·
                    refine ⟨45700079492136880621493813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30466719661424587080995875 45700079492136880621493813)
                    ·
                      refine ⟨4284382452387832558265045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45700079492136880621493813 4284382452387832558265045)
                      ·
                        rfl

theorem cell23_8343805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_8343805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343805 prefixEnd_8343805 := by exact prefixLift 8343805
  have htrace : WordTrace (prefixWord ++ tailWord_8343805) baseStart_8343805 baseEnd_8343805 := by
    simpa [prefixWord, tailWord_8343805, baseEnd_8343805] using wordTrace_append hprefix tailTrace_8343805
  have hstable : (prefixWord ++ tailWord_8343805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343805).length < 2 ^ (prefixWord ++ tailWord_8343805).sum := by decide
  have hdescent : baseEnd_8343805 < baseStart_8343805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343806 : List Nat := [4, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_8343806 : Nat := 118140960795 + 8343806 * 2 ^ 59
def prefixEnd_8343806 : Nat := 4983230072969 + 3 ^ 40 * 8343806 * 2
def baseEnd_8343806 : Nat := 4284382965868487054352541

theorem tailTrace_8343806 : CollatzResearch.WordTrace tailWord_8343806 prefixEnd_8343806 4284382965868487054352541 := by
  unfold tailWord_8343806
  simp only [CollatzResearch.WordTrace]
  refine ⟨38040450751227918182397409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202882404006548896972786181 38040450751227918182397409)
  ·
    refine ⟨28530338063420938636798057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38040450751227918182397409 28530338063420938636798057)
    ·
      refine ⟨21397753547565703977598543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28530338063420938636798057 21397753547565703977598543)
      ·
        refine ⟨32096630321348555966397815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21397753547565703977598543 32096630321348555966397815)
        ·
          refine ⟨48144945482022833949596723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32096630321348555966397815 48144945482022833949596723)
          ·
            refine ⟨72217418223034250924395085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48144945482022833949596723 72217418223034250924395085)
            ·
              refine ⟨27081531833637844096648157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72217418223034250924395085 27081531833637844096648157)
              ·
                refine ⟨10155574437614191536243059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27081531833637844096648157 10155574437614191536243059)
                ·
                  refine ⟨15233361656421287304364589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10155574437614191536243059 15233361656421287304364589)
                  ·
                    refine ⟨5712510621157982739136721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15233361656421287304364589 5712510621157982739136721)
                    ·
                      refine ⟨4284382965868487054352541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5712510621157982739136721 4284382965868487054352541)
                      ·
                        rfl

theorem cell23_8343806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_8343806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343806 prefixEnd_8343806 := by exact prefixLift 8343806
  have htrace : WordTrace (prefixWord ++ tailWord_8343806) baseStart_8343806 baseEnd_8343806 := by
    simpa [prefixWord, tailWord_8343806, baseEnd_8343806] using wordTrace_append hprefix tailTrace_8343806
  have hstable : (prefixWord ++ tailWord_8343806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343806).length < 2 ^ (prefixWord ++ tailWord_8343806).sum := by decide
  have hdescent : baseEnd_8343806 < baseStart_8343806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343819 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 4, 2, 2]
def baseStart_8343819 : Nat := 118140960795 + 8343819 * 2 ^ 59
def prefixEnd_8343819 : Nat := 4983230072969 + 3 ^ 40 * 8343819 * 2
def baseEnd_8343819 : Nat := 4284389641116995503489981

theorem tailTrace_8343819 : CollatzResearch.WordTrace tailWord_8343819 prefixEnd_8343819 4284389641116995503489981 := by
  unfold tailWord_8343819
  simp only [CollatzResearch.WordTrace]
  refine ⟨304324080158776248679402511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202882720105850832452935007 304324080158776248679402511)
  ·
    refine ⟨456486120238164373019103767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304324080158776248679402511 456486120238164373019103767)
    ·
      refine ⟨684729180357246559528655651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456486120238164373019103767 684729180357246559528655651)
      ·
        refine ⟨1027093770535869839292983477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684729180357246559528655651 1027093770535869839292983477)
        ·
          refine ⟨96290040987737797433717201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1027093770535869839292983477 96290040987737797433717201)
          ·
            refine ⟨72217530740803348075287901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96290040987737797433717201 72217530740803348075287901)
            ·
              refine ⟨27081574027801255528232963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72217530740803348075287901 27081574027801255528232963)
              ·
                refine ⟨40622361041701883292349445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27081574027801255528232963 40622361041701883292349445)
                ·
                  refine ⟨7616692695319103117315521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40622361041701883292349445 7616692695319103117315521)
                  ·
                    refine ⟨5712519521489327337986641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7616692695319103117315521 5712519521489327337986641)
                    ·
                      refine ⟨4284389641116995503489981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5712519521489327337986641 4284389641116995503489981)
                      ·
                        rfl

theorem cell23_8343819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 2, 2].length) (baseStart_8343819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343819 prefixEnd_8343819 := by exact prefixLift 8343819
  have htrace : WordTrace (prefixWord ++ tailWord_8343819) baseStart_8343819 baseEnd_8343819 := by
    simpa [prefixWord, tailWord_8343819, baseEnd_8343819] using wordTrace_append hprefix tailTrace_8343819
  have hstable : (prefixWord ++ tailWord_8343819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343819).length < 2 ^ (prefixWord ++ tailWord_8343819).sum := by decide
  have hdescent : baseEnd_8343819 < baseStart_8343819 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343825 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 7]
def baseStart_8343825 : Nat := 118140960795 + 8343825 * 2 ^ 59
def prefixEnd_8343825 : Nat := 4983230072969 + 3 ^ 40 * 8343825 * 2
def baseEnd_8343825 : Nat := 476043635777880275557217

theorem tailTrace_8343825 : CollatzResearch.WordTrace tailWord_8343825 prefixEnd_8343825 476043635777880275557217 := by
  unfold tailWord_8343825
  simp only [CollatzResearch.WordTrace]
  refine ⟨304324298996754511704120929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202882865997836341136080619 304324298996754511704120929)
  ·
    refine ⟨228243224247565883778090697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304324298996754511704120929 228243224247565883778090697)
    ·
      refine ⟨171182418185674412833568023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228243224247565883778090697 171182418185674412833568023)
      ·
        refine ⟨256773627278511619250352035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171182418185674412833568023 256773627278511619250352035)
        ·
          refine ⟨385160440917767428875528053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256773627278511619250352035 385160440917767428875528053)
          ·
            refine ⟨36108791336040696457080755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 385160440917767428875528053 36108791336040696457080755)
            ·
              refine ⟨54163187004061044685621133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36108791336040696457080755 54163187004061044685621133)
              ·
                refine ⟨20311195126522891757107925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54163187004061044685621133 20311195126522891757107925)
                ·
                  refine ⟨476043635777880275557217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20311195126522891757107925 476043635777880275557217)
                  ·
                    rfl

theorem cell23_8343825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 7].length) (baseStart_8343825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343825 prefixEnd_8343825 := by exact prefixLift 8343825
  have htrace : WordTrace (prefixWord ++ tailWord_8343825) baseStart_8343825 baseEnd_8343825 := by
    simpa [prefixWord, tailWord_8343825, baseEnd_8343825] using wordTrace_append hprefix tailTrace_8343825
  have hstable : (prefixWord ++ tailWord_8343825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343825).length < 2 ^ (prefixWord ++ tailWord_8343825).sum := by decide
  have hdescent : baseEnd_8343825 < baseStart_8343825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343842 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 7]
def baseStart_8343842 : Nat := 118140960795 + 8343842 * 2 ^ 59
def prefixEnd_8343842 : Nat := 4983230072969 + 3 ^ 40 * 8343842 * 2
def baseEnd_8343842 : Nat := 476044605685783212611375

theorem tailTrace_8343842 : CollatzResearch.WordTrace tailWord_8343842 prefixEnd_8343842 476044605685783212611375 := by
  unfold tailWord_8343842
  simp only [CollatzResearch.WordTrace]
  refine ⟨76081229759423230901872445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202883279358461949071659853 76081229759423230901872445)
  ·
    refine ⟨28530461159783711588202167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76081229759423230901872445 28530461159783711588202167)
    ·
      refine ⟨42795691739675567382303251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28530461159783711588202167 42795691739675567382303251)
      ·
        refine ⟨64193537609513351073454877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42795691739675567382303251 64193537609513351073454877)
        ·
          refine ⟨24072576603567506652545579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64193537609513351073454877 24072576603567506652545579)
          ·
            refine ⟨36108864905351259978818369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24072576603567506652545579 36108864905351259978818369)
            ·
              refine ⟨27081648679013444984113777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36108864905351259978818369 27081648679013444984113777)
              ·
                refine ⟨20311236509260083738085333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27081648679013444984113777 20311236509260083738085333)
                ·
                  refine ⟨476044605685783212611375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20311236509260083738085333 476044605685783212611375)
                  ·
                    rfl

theorem cell23_8343842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_8343842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343842 prefixEnd_8343842 := by exact prefixLift 8343842
  have htrace : WordTrace (prefixWord ++ tailWord_8343842) baseStart_8343842 baseEnd_8343842 := by
    simpa [prefixWord, tailWord_8343842, baseEnd_8343842] using wordTrace_append hprefix tailTrace_8343842
  have hstable : (prefixWord ++ tailWord_8343842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343842).length < 2 ^ (prefixWord ++ tailWord_8343842).sum := by decide
  have hdescent : baseEnd_8343842 < baseStart_8343842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343855 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 1, 7]
def baseStart_8343855 : Nat := 118140960795 + 8343855 * 2 ^ 59
def prefixEnd_8343855 : Nat := 4983230072969 + 3 ^ 40 * 8343855 * 2
def baseEnd_8343855 : Nat := 1428136042140185787546605

theorem tailTrace_8343855 : CollatzResearch.WordTrace tailWord_8343855 prefixEnd_8343855 1428136042140185787546605 := by
  unfold tailWord_8343855
  simp only [CollatzResearch.WordTrace]
  refine ⟨304325393186645826827713019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202883595457763884551808679 304325393186645826827713019)
  ·
    refine ⟨456488089779968740241569529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304325393186645826827713019 456488089779968740241569529)
    ·
      refine ⟨342366067334976555181177147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456488089779968740241569529 342366067334976555181177147)
      ·
        refine ⟨513549101002464832771765721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342366067334976555181177147 513549101002464832771765721)
        ·
          refine ⟨385161825751848624578824291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513549101002464832771765721 385161825751848624578824291)
          ·
            refine ⟨577742738627772936868236437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385161825751848624578824291 577742738627772936868236437)
            ·
              refine ⟨27081690873176856415698583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 577742738627772936868236437 27081690873176856415698583)
              ·
                refine ⟨40622536309765284623547875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27081690873176856415698583 40622536309765284623547875)
                ·
                  refine ⟨60933804464647926935321813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40622536309765284623547875 60933804464647926935321813)
                  ·
                    refine ⟨1428136042140185787546605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60933804464647926935321813 1428136042140185787546605)
                    ·
                      rfl

theorem cell23_8343855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_8343855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343855 prefixEnd_8343855 := by exact prefixLift 8343855
  have htrace : WordTrace (prefixWord ++ tailWord_8343855) baseStart_8343855 baseEnd_8343855 := by
    simpa [prefixWord, tailWord_8343855, baseEnd_8343855] using wordTrace_append hprefix tailTrace_8343855
  have hstable : (prefixWord ++ tailWord_8343855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343855).length < 2 ^ (prefixWord ++ tailWord_8343855).sum := by decide
  have hdescent : baseEnd_8343855 < baseStart_8343855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343876 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 7]
def baseStart_8343876 : Nat := 118140960795 + 8343876 * 2 ^ 59
def prefixEnd_8343876 : Nat := 4983230072969 + 3 ^ 40 * 8343876 * 2
def baseEnd_8343876 : Nat := 476046545501589086719691

theorem tailTrace_8343876 : CollatzResearch.WordTrace tailWord_8343876 prefixEnd_8343876 476046545501589086719691 := by
  unfold tailWord_8343876
  simp only [CollatzResearch.WordTrace]
  refine ⟨152163079559784873707113741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202884106079713164942818321 152163079559784873707113741)
  ·
    refine ⟨57061154834919327640167653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152163079559784873707113741 57061154834919327640167653)
    ·
      refine ⟨10698966531547373932531435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57061154834919327640167653 10698966531547373932531435)
      ·
        refine ⟨16048449797321060898797153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10698966531547373932531435 16048449797321060898797153)
        ·
          refine ⟨12036337347990795674097865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16048449797321060898797153 12036337347990795674097865)
          ·
            refine ⟨9027253010993096755573399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12036337347990795674097865 9027253010993096755573399)
            ·
              refine ⟨13540879516489645133360099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9027253010993096755573399 13540879516489645133360099)
              ·
                refine ⟨20311319274734467700040149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13540879516489645133360099 20311319274734467700040149)
                ·
                  refine ⟨476046545501589086719691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20311319274734467700040149 476046545501589086719691)
                  ·
                    rfl

theorem cell23_8343876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_8343876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343876 prefixEnd_8343876 := by exact prefixLift 8343876
  have htrace : WordTrace (prefixWord ++ tailWord_8343876) baseStart_8343876 baseEnd_8343876 := by
    simpa [prefixWord, tailWord_8343876, baseEnd_8343876] using wordTrace_append hprefix tailTrace_8343876
  have hstable : (prefixWord ++ tailWord_8343876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343876).length < 2 ^ (prefixWord ++ tailWord_8343876).sum := by decide
  have hdescent : baseEnd_8343876 < baseStart_8343876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343905 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_8343905 : Nat := 118140960795 + 8343905 * 2 ^ 59
def prefixEnd_8343905 : Nat := 4983230072969 + 3 ^ 40 * 8343905 * 2
def baseEnd_8343905 : Nat := 4284433800453282167014585

theorem tailTrace_8343905 : CollatzResearch.WordTrace tailWord_8343905 prefixEnd_8343905 4284433800453282167014585 := by
  unfold tailWord_8343905
  simp only [CollatzResearch.WordTrace]
  refine ⟨304327216836464685367033169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202884811224309790244688779 304327216836464685367033169)
  ·
    refine ⟨228245412627348514025274877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304327216836464685367033169 228245412627348514025274877)
    ·
      refine ⟨85592029735255692759478079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228245412627348514025274877 85592029735255692759478079)
      ·
        refine ⟨128388044602883539139217119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85592029735255692759478079 128388044602883539139217119)
        ·
          refine ⟨192582066904325308708825679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128388044602883539139217119 192582066904325308708825679)
          ·
            refine ⟨288873100356487963063238519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192582066904325308708825679 288873100356487963063238519)
            ·
              refine ⟨433309650534731944594857779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288873100356487963063238519 433309650534731944594857779)
              ·
                refine ⟨649964475802097916892286669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433309650534731944594857779 649964475802097916892286669)
                ·
                  refine ⟨243736678425786718834607501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649964475802097916892286669 243736678425786718834607501)
                  ·
                    refine ⟨91401254409670019562977813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243736678425786718834607501 91401254409670019562977813)
                    ·
                      refine ⟨4284433800453282167014585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91401254409670019562977813 4284433800453282167014585)
                      ·
                        rfl

theorem cell23_8343905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_8343905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343905 prefixEnd_8343905 := by exact prefixLift 8343905
  have htrace : WordTrace (prefixWord ++ tailWord_8343905) baseStart_8343905 baseEnd_8343905 := by
    simpa [prefixWord, tailWord_8343905, baseEnd_8343905] using wordTrace_append hprefix tailTrace_8343905
  have hstable : (prefixWord ++ tailWord_8343905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343905).length < 2 ^ (prefixWord ++ tailWord_8343905).sum := by decide
  have hdescent : baseEnd_8343905 < baseStart_8343905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343909 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 2, 1, 4]
def baseStart_8343909 : Nat := 118140960795 + 8343909 * 2 ^ 59
def prefixEnd_8343909 : Nat := 4983230072969 + 3 ^ 40 * 8343909 * 2
def baseEnd_8343909 : Nat := 4284435854375900151364567

theorem tailTrace_8343909 : CollatzResearch.WordTrace tailWord_8343909 prefixEnd_8343909 4284435854375900151364567 := by
  unfold tailWord_8343909
  simp only [CollatzResearch.WordTrace]
  refine ⟨304327362728450194050178781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202884908485633462700119187 304327362728450194050178781)
  ·
    refine ⟨114122761023168822768817043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304327362728450194050178781 114122761023168822768817043)
    ·
      refine ⟨171184141534753234153225565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114122761023168822768817043 171184141534753234153225565)
      ·
        refine ⟨64194053075532462807459587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171184141534753234153225565 64194053075532462807459587)
        ·
          refine ⟨96291079613298694211189381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64194053075532462807459587 96291079613298694211189381)
          ·
            refine ⟨18054577427493505164598009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96291079613298694211189381 18054577427493505164598009)
            ·
              refine ⟨13540933070620128873448507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18054577427493505164598009 13540933070620128873448507)
              ·
                refine ⟨20311399605930193310172761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13540933070620128873448507 20311399605930193310172761)
                ·
                  refine ⟨15233549704447644982629571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20311399605930193310172761 15233549704447644982629571)
                  ·
                    refine ⟨22850324556671467473944357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15233549704447644982629571 22850324556671467473944357)
                    ·
                      refine ⟨4284435854375900151364567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22850324556671467473944357 4284435854375900151364567)
                      ·
                        rfl

theorem cell23_8343909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_8343909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343909 prefixEnd_8343909 := by exact prefixLift 8343909
  have htrace : WordTrace (prefixWord ++ tailWord_8343909) baseStart_8343909 baseEnd_8343909 := by
    simpa [prefixWord, tailWord_8343909, baseEnd_8343909] using wordTrace_append hprefix tailTrace_8343909
  have hstable : (prefixWord ++ tailWord_8343909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343909).length < 2 ^ (prefixWord ++ tailWord_8343909).sum := by decide
  have hdescent : baseEnd_8343909 < baseStart_8343909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343935 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 8]
def baseStart_8343935 : Nat := 118140960795 + 8343935 * 2 ^ 59
def prefixEnd_8343935 : Nat := 4983230072969 + 3 ^ 40 * 8343935 * 2
def baseEnd_8343935 : Nat := 4284449204872917049639447

theorem tailTrace_8343935 : CollatzResearch.WordTrace tailWord_8343935 prefixEnd_8343935 4284449204872917049639447 := by
  unfold tailWord_8343935
  simp only [CollatzResearch.WordTrace]
  refine ⟨304328311026356000490625259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202885540684237333660416839 304328311026356000490625259)
  ·
    refine ⟨456492466539534000735937889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304328311026356000490625259 456492466539534000735937889)
    ·
      refine ⟨342369349904650500551953417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456492466539534000735937889 342369349904650500551953417)
      ·
        refine ⟨256777012428487875413965063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342369349904650500551953417 256777012428487875413965063)
        ·
          refine ⟨385165518642731813120947595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256777012428487875413965063 385165518642731813120947595)
          ·
            refine ⟨577748277964097719681421393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385165518642731813120947595 577748277964097719681421393)
            ·
              refine ⟨433311208473073289761066045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577748277964097719681421393 433311208473073289761066045)
              ·
                refine ⟨162491703177402483660399767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433311208473073289761066045 162491703177402483660399767)
                ·
                  refine ⟨243737554766103725490599651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162491703177402483660399767 243737554766103725490599651)
                  ·
                    refine ⟨365606332149155588235899477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243737554766103725490599651 365606332149155588235899477)
                    ·
                      refine ⟨4284449204872917049639447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 365606332149155588235899477 4284449204872917049639447)
                      ·
                        rfl

theorem cell23_8343935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_8343935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343935 prefixEnd_8343935 := by exact prefixLift 8343935
  have htrace : WordTrace (prefixWord ++ tailWord_8343935) baseStart_8343935 baseEnd_8343935 := by
    simpa [prefixWord, tailWord_8343935, baseEnd_8343935] using wordTrace_append hprefix tailTrace_8343935
  have hstable : (prefixWord ++ tailWord_8343935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343935).length < 2 ^ (prefixWord ++ tailWord_8343935).sum := by decide
  have hdescent : baseEnd_8343935 < baseStart_8343935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343959 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 5, 1, 3]
def baseStart_8343959 : Nat := 118140960795 + 8343959 * 2 ^ 59
def prefixEnd_8343959 : Nat := 4983230072969 + 3 ^ 40 * 8343959 * 2
def baseEnd_8343959 : Nat := 4284461528408624955739337

theorem tailTrace_8343959 : CollatzResearch.WordTrace tailWord_8343959 prefixEnd_8343959 4284461528408624955739337 := by
  unfold tailWord_8343959
  simp only [CollatzResearch.WordTrace]
  refine ⟨304329186378269052589498931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202886124252179368392999287 304329186378269052589498931)
  ·
    refine ⟨456493779567403578884248397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304329186378269052589498931 456493779567403578884248397)
    ·
      refine ⟨171185167337776342081593149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456493779567403578884248397 171185167337776342081593149)
      ·
        refine ⟨64194437751666128280597431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171185167337776342081593149 64194437751666128280597431)
        ·
          refine ⟨96291656627499192420896147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64194437751666128280597431 96291656627499192420896147)
          ·
            refine ⟨144437484941248788631344221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96291656627499192420896147 144437484941248788631344221)
            ·
              refine ⟨54164056852968295736754083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144437484941248788631344221 54164056852968295736754083)
              ·
                refine ⟨81246085279452443605131125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54164056852968295736754083 81246085279452443605131125)
                ·
                  refine ⟨7616820494948666587981043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81246085279452443605131125 7616820494948666587981043)
                  ·
                    refine ⟨11425230742422999881971565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7616820494948666587981043 11425230742422999881971565)
                    ·
                      refine ⟨4284461528408624955739337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11425230742422999881971565 4284461528408624955739337)
                      ·
                        rfl

theorem cell23_8343959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_8343959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343959 prefixEnd_8343959 := by exact prefixLift 8343959
  have htrace : WordTrace (prefixWord ++ tailWord_8343959) baseStart_8343959 baseEnd_8343959 := by
    simpa [prefixWord, tailWord_8343959, baseEnd_8343959] using wordTrace_append hprefix tailTrace_8343959
  have hstable : (prefixWord ++ tailWord_8343959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343959).length < 2 ^ (prefixWord ++ tailWord_8343959).sum := by decide
  have hdescent : baseEnd_8343959 < baseStart_8343959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8343993 : List Nat := [1, 2, 1, 4, 3, 1, 2, 4, 1, 1, 3]
def baseStart_8343993 : Nat := 118140960795 + 8343993 * 2 ^ 59
def prefixEnd_8343993 : Nat := 4983230072969 + 3 ^ 40 * 8343993 * 2
def baseEnd_8343993 : Nat := 4284478986750877822714181

theorem tailTrace_8343993 : CollatzResearch.WordTrace tailWord_8343993 prefixEnd_8343993 4284478986750877822714181 := by
  unfold tailWord_8343993
  simp only [CollatzResearch.WordTrace]
  refine ⟨304330426460145876396236633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202886950973430584264157755 304330426460145876396236633)
  ·
    refine ⟨228247819845109407297177475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304330426460145876396236633 228247819845109407297177475)
    ·
      refine ⟨342371729767664110945766213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228247819845109407297177475 342371729767664110945766213)
      ·
        refine ⟨64194699331437020802331165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342371729767664110945766213 64194699331437020802331165)
        ·
          refine ⟨24073012249288882800874187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64194699331437020802331165 24073012249288882800874187)
          ·
            refine ⟨36109518373933324201311281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24073012249288882800874187 36109518373933324201311281)
            ·
              refine ⟨27082138780449993150983461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36109518373933324201311281 27082138780449993150983461)
              ·
                refine ⟨5077901021334373715809399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27082138780449993150983461 5077901021334373715809399)
                ·
                  refine ⟨7616851532001560573714099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077901021334373715809399 7616851532001560573714099)
                  ·
                    refine ⟨11425277298002340860571149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7616851532001560573714099 11425277298002340860571149)
                    ·
                      refine ⟨4284478986750877822714181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11425277298002340860571149 4284478986750877822714181)
                      ·
                        rfl

theorem cell23_8343993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_8343993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8343993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8343993 prefixEnd_8343993 := by exact prefixLift 8343993
  have htrace : WordTrace (prefixWord ++ tailWord_8343993) baseStart_8343993 baseEnd_8343993 := by
    simpa [prefixWord, tailWord_8343993, baseEnd_8343993] using wordTrace_append hprefix tailTrace_8343993
  have hstable : (prefixWord ++ tailWord_8343993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8343993).length < 2 ^ (prefixWord ++ tailWord_8343993).sum := by decide
  have hdescent : baseEnd_8343993 < baseStart_8343993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8343993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344009 : List Nat := [1, 2, 1, 1, 2, 1, 4, 5, 2, 4]
def baseStart_8344009 : Nat := 118140960795 + 8344009 * 2 ^ 59
def prefixEnd_8344009 : Nat := 4983230072969 + 3 ^ 40 * 8344009 * 2
def baseEnd_8344009 : Nat := 1428162400813783253371369

theorem tailTrace_8344009 : CollatzResearch.WordTrace tailWord_8344009 prefixEnd_8344009 1428162400813783253371369 := by
  unfold tailWord_8344009
  simp only [CollatzResearch.WordTrace]
  refine ⟨304331010028087911128819081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202887340018725274085879387 304331010028087911128819081)
  ·
    refine ⟨228248257521065933346614311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304331010028087911128819081 228248257521065933346614311)
    ·
      refine ⟨342372386281598900019921467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228248257521065933346614311 342372386281598900019921467)
      ·
        refine ⟨513558579422398350029882201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342372386281598900019921467 513558579422398350029882201)
        ·
          refine ⟨385168934566798762522411651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513558579422398350029882201 385168934566798762522411651)
          ·
            refine ⟨577753401850198143783617477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385168934566798762522411651 577753401850198143783617477)
            ·
              refine ⟨108328762846912151959428277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 577753401850198143783617477 108328762846912151959428277)
              ·
                refine ⟨10155821516898014246196401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108328762846912151959428277 10155821516898014246196401)
                ·
                  refine ⟨7616866137673510684647301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10155821516898014246196401 7616866137673510684647301)
                  ·
                    refine ⟨1428162400813783253371369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7616866137673510684647301 1428162400813783253371369)
                    ·
                      rfl

theorem cell23_8344009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 4].length) (baseStart_8344009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344009 prefixEnd_8344009 := by exact prefixLift 8344009
  have htrace : WordTrace (prefixWord ++ tailWord_8344009) baseStart_8344009 baseEnd_8344009 := by
    simpa [prefixWord, tailWord_8344009, baseEnd_8344009] using wordTrace_append hprefix tailTrace_8344009
  have hstable : (prefixWord ++ tailWord_8344009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344009).length < 2 ^ (prefixWord ++ tailWord_8344009).sum := by decide
  have hdescent : baseEnd_8344009 < baseStart_8344009 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344029 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_8344029 : Nat := 118140960795 + 8344029 * 2 ^ 59
def prefixEnd_8344029 : Nat := 4983230072969 + 3 ^ 40 * 8344029 * 2
def baseEnd_8344029 : Nat := 4284497472054439681864015

theorem tailTrace_8344029 : CollatzResearch.WordTrace tailWord_8344029 prefixEnd_8344029 4284497472054439681864015 := by
  unfold tailWord_8344029
  simp only [CollatzResearch.WordTrace]
  refine ⟨304331739488015454544547141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202887826325343636363031427 304331739488015454544547141)
  ·
    refine ⟨57062201154002897727102589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304331739488015454544547141 57062201154002897727102589)
    ·
      refine ⟨21398325432751086647663471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57062201154002897727102589 21398325432751086647663471)
      ·
        refine ⟨32097488149126629971495207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21398325432751086647663471 32097488149126629971495207)
        ·
          refine ⟨48146232223689944957242811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32097488149126629971495207 48146232223689944957242811)
          ·
            refine ⟨72219348335534917435864217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48146232223689944957242811 72219348335534917435864217)
            ·
              refine ⟨54164511251651188076898163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72219348335534917435864217 54164511251651188076898163)
              ·
                refine ⟨81246766877476782115347245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54164511251651188076898163 81246766877476782115347245)
                ·
                  refine ⟨30467537579053793293255217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81246766877476782115347245 30467537579053793293255217)
                  ·
                    refine ⟨22850653184290344969941413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30467537579053793293255217 22850653184290344969941413)
                    ·
                      refine ⟨4284497472054439681864015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22850653184290344969941413 4284497472054439681864015)
                      ·
                        rfl

theorem cell23_8344029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_8344029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344029 prefixEnd_8344029 := by exact prefixLift 8344029
  have htrace : WordTrace (prefixWord ++ tailWord_8344029) baseStart_8344029 baseEnd_8344029 := by
    simpa [prefixWord, tailWord_8344029, baseEnd_8344029] using wordTrace_append hprefix tailTrace_8344029
  have hstable : (prefixWord ++ tailWord_8344029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344029).length < 2 ^ (prefixWord ++ tailWord_8344029).sum := by decide
  have hdescent : baseEnd_8344029 < baseStart_8344029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344072 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_8344072 : Nat := 118140960795 + 8344072 * 2 ^ 59
def prefixEnd_8344072 : Nat := 4983230072969 + 3 ^ 40 * 8344072 * 2
def baseEnd_8344072 : Nat := 4284519551722583013626317

theorem tailTrace_8344072 : CollatzResearch.WordTrace tailWord_8344072 prefixEnd_8344072 4284519551722583013626317 := by
  unfold tailWord_8344072
  simp only [CollatzResearch.WordTrace]
  refine ⟨152166653913429836444181235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202888871884573115258908313 152166653913429836444181235)
  ·
    refine ⟨228249980870144754666271853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152166653913429836444181235 228249980870144754666271853)
    ·
      refine ⟨85593742826304282999851945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228249980870144754666271853 85593742826304282999851945)
      ·
        refine ⟨64195307119728212249888959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85593742826304282999851945 64195307119728212249888959)
        ·
          refine ⟨96292960679592318374833439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64195307119728212249888959 96292960679592318374833439)
          ·
            refine ⟨144439441019388477562250159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96292960679592318374833439 144439441019388477562250159)
            ·
              refine ⟨216659161529082716343375239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144439441019388477562250159 216659161529082716343375239)
              ·
                refine ⟨324988742293624074515062859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216659161529082716343375239 324988742293624074515062859)
                ·
                  refine ⟨487483113440436111772594289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324988742293624074515062859 487483113440436111772594289)
                  ·
                    refine ⟨365612335080327083829445717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 487483113440436111772594289 365612335080327083829445717)
                    ·
                      refine ⟨4284519551722583013626317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 365612335080327083829445717 4284519551722583013626317)
                      ·
                        rfl

theorem cell23_8344072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_8344072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344072 prefixEnd_8344072 := by exact prefixLift 8344072
  have htrace : WordTrace (prefixWord ++ tailWord_8344072) baseStart_8344072 baseEnd_8344072 := by
    simpa [prefixWord, tailWord_8344072, baseEnd_8344072] using wordTrace_append hprefix tailTrace_8344072
  have hstable : (prefixWord ++ tailWord_8344072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344072).length < 2 ^ (prefixWord ++ tailWord_8344072).sum := by decide
  have hdescent : baseEnd_8344072 < baseStart_8344072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344119 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_8344119 : Nat := 118140960795 + 8344119 * 2 ^ 59
def prefixEnd_8344119 : Nat := 4983230072969 + 3 ^ 40 * 8344119 * 2
def baseEnd_8344119 : Nat := 4284543685313344329738601

theorem tailTrace_8344119 : CollatzResearch.WordTrace tailWord_8344119 prefixEnd_8344119 4284543685313344329738601 := by
  unfold tailWord_8344119
  simp only [CollatzResearch.WordTrace]
  refine ⟨304335022057689399915323411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202890014705126266610215607 304335022057689399915323411)
  ·
    refine ⟨456502533086534099872985117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304335022057689399915323411 456502533086534099872985117)
    ·
      refine ⟨171188449907450287452369419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456502533086534099872985117 171188449907450287452369419)
      ·
        refine ⟨256782674861175431178554129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171188449907450287452369419 256782674861175431178554129)
        ·
          refine ⟨192587006145881573383915597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256782674861175431178554129 192587006145881573383915597)
          ·
            refine ⟨72220127304705590018968349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192587006145881573383915597 72220127304705590018968349)
            ·
              refine ⟨27082547739264596257113131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72220127304705590018968349 27082547739264596257113131)
              ·
                refine ⟨40623821608896894385669697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27082547739264596257113131 40623821608896894385669697)
                ·
                  refine ⟨30467866206672670789252273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40623821608896894385669697 30467866206672670789252273)
                  ·
                    refine ⟨22850899655004503091939205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30467866206672670789252273 22850899655004503091939205)
                    ·
                      refine ⟨4284543685313344329738601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22850899655004503091939205 4284543685313344329738601)
                      ·
                        rfl

theorem cell23_8344119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_8344119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344119 prefixEnd_8344119 := by exact prefixLift 8344119
  have htrace : WordTrace (prefixWord ++ tailWord_8344119) baseStart_8344119 baseEnd_8344119 := by
    simpa [prefixWord, tailWord_8344119, baseEnd_8344119] using wordTrace_append hprefix tailTrace_8344119
  have hstable : (prefixWord ++ tailWord_8344119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344119).length < 2 ^ (prefixWord ++ tailWord_8344119).sum := by decide
  have hdescent : baseEnd_8344119 < baseStart_8344119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344129 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 9]
def baseStart_8344129 : Nat := 118140960795 + 8344129 * 2 ^ 59
def prefixEnd_8344129 : Nat := 4983230072969 + 3 ^ 40 * 8344129 * 2
def baseEnd_8344129 : Nat := 476060980013321032290395

theorem tailTrace_8344129 : CollatzResearch.WordTrace tailWord_8344129 prefixEnd_8344129 476060980013321032290395 := by
  unfold tailWord_8344129
  simp only [CollatzResearch.WordTrace]
  refine ⟨304335386787653171623187441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202890257858435447748791627 304335386787653171623187441)
  ·
    refine ⟨228251540090739878717390581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304335386787653171623187441 228251540090739878717390581)
    ·
      refine ⟨21398581883506863629755367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228251540090739878717390581 21398581883506863629755367)
      ·
        refine ⟨32097872825260295444633051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21398581883506863629755367 32097872825260295444633051)
        ·
          refine ⟨48146809237890443166949577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32097872825260295444633051 48146809237890443166949577)
          ·
            refine ⟨36110106928417832375212183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48146809237890443166949577 36110106928417832375212183)
            ·
              refine ⟨54165160392626748562818275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36110106928417832375212183 54165160392626748562818275)
              ·
                refine ⟨81247740588940122844227413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54165160392626748562818275 81247740588940122844227413)
                ·
                  refine ⟨476060980013321032290395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81247740588940122844227413 476060980013321032290395)
                  ·
                    rfl

theorem cell23_8344129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 9].length) (baseStart_8344129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344129 prefixEnd_8344129 := by exact prefixLift 8344129
  have htrace : WordTrace (prefixWord ++ tailWord_8344129) baseStart_8344129 baseEnd_8344129 := by
    simpa [prefixWord, tailWord_8344129, baseEnd_8344129] using wordTrace_append hprefix tailTrace_8344129
  have hstable : (prefixWord ++ tailWord_8344129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344129).length < 2 ^ (prefixWord ++ tailWord_8344129).sum := by decide
  have hdescent : baseEnd_8344129 < baseStart_8344129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344159 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 2, 5]
def baseStart_8344159 : Nat := 118140960795 + 8344159 * 2 ^ 59
def prefixEnd_8344159 : Nat := 4983230072969 + 3 ^ 40 * 8344159 * 2
def baseEnd_8344159 : Nat := 1428188074846508057746139

theorem tailTrace_8344159 : CollatzResearch.WordTrace tailWord_8344159 prefixEnd_8344159 1428188074846508057746139 := by
  unfold tailWord_8344159
  simp only [CollatzResearch.WordTrace]
  refine ⟨304336480977544486746779531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202890987318362991164519687 304336480977544486746779531)
  ·
    refine ⟨456504721466316730120169297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304336480977544486746779531 456504721466316730120169297)
    ·
      refine ⟨342378541099737547590126973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456504721466316730120169297 342378541099737547590126973)
      ·
        refine ⟨128391952912401580346297615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342378541099737547590126973 128391952912401580346297615)
        ·
          refine ⟨192587929368602370519446423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128391952912401580346297615 192587929368602370519446423)
          ·
            refine ⟨288881894052903555779169635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192587929368602370519446423 288881894052903555779169635)
            ·
              refine ⟨433322841079355333668754453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288881894052903555779169635 433322841079355333668754453)
              ·
                refine ⟨20312008175594781265722865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 433322841079355333668754453 20312008175594781265722865)
                ·
                  refine ⟨15234006131696085949292149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20312008175594781265722865 15234006131696085949292149)
                  ·
                    refine ⟨1428188074846508057746139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15234006131696085949292149 1428188074846508057746139)
                    ·
                      rfl

theorem cell23_8344159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 5].length) (baseStart_8344159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344159 prefixEnd_8344159 := by exact prefixLift 8344159
  have htrace : WordTrace (prefixWord ++ tailWord_8344159) baseStart_8344159 baseEnd_8344159 := by
    simpa [prefixWord, tailWord_8344159, baseEnd_8344159] using wordTrace_append hprefix tailTrace_8344159
  have hstable : (prefixWord ++ tailWord_8344159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344159).length < 2 ^ (prefixWord ++ tailWord_8344159).sum := by decide
  have hdescent : baseEnd_8344159 < baseStart_8344159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344179 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 4]
def baseStart_8344179 : Nat := 118140960795 + 8344179 * 2 ^ 59
def prefixEnd_8344179 : Nat := 4983230072969 + 3 ^ 40 * 8344179 * 2
def baseEnd_8344179 : Nat := 4284574494152614094988325

theorem tailTrace_8344179 : CollatzResearch.WordTrace tailWord_8344179 prefixEnd_8344179 4284574494152614094988325 := by
  unfold tailWord_8344179
  simp only [CollatzResearch.WordTrace]
  refine ⟨304337210437472030162507591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202891473624981353441671727 304337210437472030162507591)
  ·
    refine ⟨456505815656208045243761387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304337210437472030162507591 456505815656208045243761387)
    ·
      refine ⟨684758723484312067865642081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456505815656208045243761387 684758723484312067865642081)
      ·
        refine ⟨513569042613234050899231561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684758723484312067865642081 513569042613234050899231561)
        ·
          refine ⟨385176781959925538174423671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513569042613234050899231561 385176781959925538174423671)
          ·
            refine ⟨577765172939888307261635507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385176781959925538174423671 577765172939888307261635507)
            ·
              refine ⟨866647759409832460892453261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577765172939888307261635507 866647759409832460892453261)
              ·
                refine ⟨324992909778687172834669973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 866647759409832460892453261 324992909778687172834669973)
                ·
                  refine ⟨15234042645875961226625155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 324992909778687172834669973 15234042645875961226625155)
                  ·
                    refine ⟨22851063968813941839937733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15234042645875961226625155 22851063968813941839937733)
                    ·
                      refine ⟨4284574494152614094988325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22851063968813941839937733 4284574494152614094988325)
                      ·
                        rfl

theorem cell23_8344179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_8344179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344179 prefixEnd_8344179 := by exact prefixLift 8344179
  have htrace : WordTrace (prefixWord ++ tailWord_8344179) baseStart_8344179 baseEnd_8344179 := by
    simpa [prefixWord, tailWord_8344179, baseEnd_8344179] using wordTrace_append hprefix tailTrace_8344179
  have hstable : (prefixWord ++ tailWord_8344179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344179).length < 2 ^ (prefixWord ++ tailWord_8344179).sum := by decide
  have hdescent : baseEnd_8344179 < baseStart_8344179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344196 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_8344196 : Nat := 118140960795 + 8344196 * 2 ^ 59
def prefixEnd_8344196 : Nat := 4983230072969 + 3 ^ 40 * 8344196 * 2
def baseEnd_8344196 : Nat := 4284583223323740528475747

theorem tailTrace_8344196 : CollatzResearch.WordTrace tailWord_8344196 prefixEnd_8344196 4284583223323740528475747 := by
  unfold tailWord_8344196
  simp only [CollatzResearch.WordTrace]
  refine ⟨152168915239205221032938221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202891886985606961377250961 152168915239205221032938221)
  ·
    refine ⟨57063343214701957887351833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152168915239205221032938221 57063343214701957887351833)
    ·
      refine ⟨42797507411026468415513875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57063343214701957887351833 42797507411026468415513875)
      ·
        refine ⟨64196261116539702623270813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42797507411026468415513875 64196261116539702623270813)
        ·
          refine ⟨24073597918702388483726555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64196261116539702623270813 24073597918702388483726555)
          ·
            refine ⟨36110396878053582725589833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24073597918702388483726555 36110396878053582725589833)
            ·
              refine ⟨27082797658540187044192375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36110396878053582725589833 27082797658540187044192375)
              ·
                refine ⟨40624196487810280566288563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27082797658540187044192375 40624196487810280566288563)
                ·
                  refine ⟨60936294731715420849432845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40624196487810280566288563 60936294731715420849432845)
                  ·
                    refine ⟨22851110524393282818537317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60936294731715420849432845 22851110524393282818537317)
                    ·
                      refine ⟨4284583223323740528475747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22851110524393282818537317 4284583223323740528475747)
                      ·
                        rfl

theorem cell23_8344196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_8344196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344196 prefixEnd_8344196 := by exact prefixLift 8344196
  have htrace : WordTrace (prefixWord ++ tailWord_8344196) baseStart_8344196 baseEnd_8344196 := by
    simpa [prefixWord, tailWord_8344196, baseEnd_8344196] using wordTrace_append hprefix tailTrace_8344196
  have hstable : (prefixWord ++ tailWord_8344196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344196).length < 2 ^ (prefixWord ++ tailWord_8344196).sum := by decide
  have hdescent : baseEnd_8344196 < baseStart_8344196 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344273 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 2, 3, 2]
def baseStart_8344273 : Nat := 118140960795 + 8344273 * 2 ^ 59
def prefixEnd_8344273 : Nat := 4983230072969 + 3 ^ 40 * 8344273 * 2
def baseEnd_8344273 : Nat := 4284622761334136727212893

theorem tailTrace_8344273 : CollatzResearch.WordTrace tailWord_8344273 prefixEnd_8344273 4284622761334136727212893 := by
  unfold tailWord_8344273
  simp only [CollatzResearch.WordTrace]
  refine ⟨304340638899131484216429473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202893759266087656144286315 304340638899131484216429473)
  ·
    refine ⟨228255479174348613162322105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304340638899131484216429473 228255479174348613162322105)
    ·
      refine ⟨171191609380761459871741579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228255479174348613162322105 171191609380761459871741579)
      ·
        refine ⟨256787414071142189807612369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171191609380761459871741579 256787414071142189807612369)
        ·
          refine ⟨192590560553356642355709277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256787414071142189807612369 192590560553356642355709277)
          ·
            refine ⟨72221460207508740883390979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192590560553356642355709277 72221460207508740883390979)
            ·
              refine ⟨108332190311263111325086469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72221460207508740883390979 108332190311263111325086469)
              ·
                refine ⟨20312285683361833373453713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108332190311263111325086469 20312285683361833373453713)
                ·
                  refine ⟨15234214262521375030090285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20312285683361833373453713 15234214262521375030090285)
                  ·
                    refine ⟨5712830348445515636283857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15234214262521375030090285 5712830348445515636283857)
                    ·
                      refine ⟨4284622761334136727212893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5712830348445515636283857 4284622761334136727212893)
                      ·
                        rfl

theorem cell23_8344273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 3, 2].length) (baseStart_8344273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344273 prefixEnd_8344273 := by exact prefixLift 8344273
  have htrace : WordTrace (prefixWord ++ tailWord_8344273) baseStart_8344273 baseEnd_8344273 := by
    simpa [prefixWord, tailWord_8344273, baseEnd_8344273] using wordTrace_append hprefix tailTrace_8344273
  have hstable : (prefixWord ++ tailWord_8344273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344273).length < 2 ^ (prefixWord ++ tailWord_8344273).sum := by decide
  have hdescent : baseEnd_8344273 < baseStart_8344273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344274 : List Nat := [3, 2, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_8344274 : Nat := 118140960795 + 8344274 * 2 ^ 59
def prefixEnd_8344274 : Nat := 4983230072969 + 3 ^ 40 * 8344274 * 2
def baseEnd_8344274 : Nat := 1428207758271597074433463

theorem tailTrace_8344274 : CollatzResearch.WordTrace tailWord_8344274 prefixEnd_8344274 1428207758271597074433463 := by
  unfold tailWord_8344274
  simp only [CollatzResearch.WordTrace]
  refine ⟨76085168843031965346803969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202893783581418574258143917 76085168843031965346803969)
  ·
    refine ⟨57063876632273974010102977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76085168843031965346803969 57063876632273974010102977)
    ·
      refine ⟨42797907474205480507577233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57063876632273974010102977 42797907474205480507577233)
      ·
        refine ⟨32098430605654110380682925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42797907474205480507577233 32098430605654110380682925)
        ·
          refine ⟨12036911477120291392756097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32098430605654110380682925 12036911477120291392756097)
          ·
            refine ⟨9027683607840218544567073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12036911477120291392756097 9027683607840218544567073)
            ·
              refine ⟨6770762705880163908425305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9027683607840218544567073 6770762705880163908425305)
              ·
                refine ⟨5078072029410122931318979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6770762705880163908425305 5078072029410122931318979)
                ·
                  refine ⟨7617108044115184396978469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5078072029410122931318979 7617108044115184396978469)
                  ·
                    refine ⟨1428207758271597074433463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7617108044115184396978469 1428207758271597074433463)
                    ·
                      rfl

theorem cell23_8344274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_8344274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344274 prefixEnd_8344274 := by exact prefixLift 8344274
  have htrace : WordTrace (prefixWord ++ tailWord_8344274) baseStart_8344274 baseEnd_8344274 := by
    simpa [prefixWord, tailWord_8344274, baseEnd_8344274] using wordTrace_append hprefix tailTrace_8344274
  have hstable : (prefixWord ++ tailWord_8344274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344274).length < 2 ^ (prefixWord ++ tailWord_8344274).sum := by decide
  have hdescent : baseEnd_8344274 < baseStart_8344274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344337 : List Nat := [1, 2, 2, 1, 1, 3, 4, 4, 1, 2, 2]
def baseStart_8344337 : Nat := 118140960795 + 8344337 * 2 ^ 59
def prefixEnd_8344337 : Nat := 4983230072969 + 3 ^ 40 * 8344337 * 2
def baseEnd_8344337 : Nat := 4284655624096024476812599

theorem tailTrace_8344337 : CollatzResearch.WordTrace tailWord_8344337 prefixEnd_8344337 4284655624096024476812599 := by
  unfold tailWord_8344337
  simp only [CollatzResearch.WordTrace]
  refine ⟨304342973170899623146759265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202895315447266415431172843 304342973170899623146759265)
  ·
    refine ⟨228257229878174717360069449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304342973170899623146759265 228257229878174717360069449)
    ·
      refine ⟨171192922408631038020052087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228257229878174717360069449 171192922408631038020052087)
      ·
        refine ⟨256789383612946557030078131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171192922408631038020052087 256789383612946557030078131)
        ·
          refine ⟨385184075419419835545117197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256789383612946557030078131 385184075419419835545117197)
          ·
            refine ⟨144444028282282438329418949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385184075419419835545117197 144444028282282438329418949)
            ·
              refine ⟨27083255302927957186766053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144444028282282438329418949 27083255302927957186766053)
              ·
                refine ⟨5078110369298991972518635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27083255302927957186766053 5078110369298991972518635)
                ·
                  refine ⟨7617165553948487958777953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5078110369298991972518635 7617165553948487958777953)
                  ·
                    refine ⟨5712874165461365969083465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7617165553948487958777953 5712874165461365969083465)
                    ·
                      refine ⟨4284655624096024476812599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5712874165461365969083465 4284655624096024476812599)
                      ·
                        rfl

theorem cell23_8344337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 1, 2, 2].length) (baseStart_8344337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344337 prefixEnd_8344337 := by exact prefixLift 8344337
  have htrace : WordTrace (prefixWord ++ tailWord_8344337) baseStart_8344337 baseEnd_8344337 := by
    simpa [prefixWord, tailWord_8344337, baseEnd_8344337] using wordTrace_append hprefix tailTrace_8344337
  have hstable : (prefixWord ++ tailWord_8344337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344337).length < 2 ^ (prefixWord ++ tailWord_8344337).sum := by decide
  have hdescent : baseEnd_8344337 < baseStart_8344337 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344388 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_8344388 : Nat := 118140960795 + 8344388 * 2 ^ 59
def prefixEnd_8344388 : Nat := 4983230072969 + 3 ^ 40 * 8344388 * 2
def baseEnd_8344388 : Nat := 4284681811609403777274865

theorem tailTrace_8344388 : CollatzResearch.WordTrace tailWord_8344388 prefixEnd_8344388 4284681811609403777274865 := by
  unfold tailWord_8344388
  simp only [CollatzResearch.WordTrace]
  refine ⟨152172416646857429428432909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202896555529143239237910545 152172416646857429428432909)
  ·
    refine ⟨57064656242571536035662341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152172416646857429428432909 57064656242571536035662341)
    ·
      refine ⟨10699623045482163006686689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57064656242571536035662341 10699623045482163006686689)
      ·
        refine ⟨8024717284111622255015017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10699623045482163006686689 8024717284111622255015017)
        ·
          refine ⟨6018537963083716691261263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8024717284111622255015017 6018537963083716691261263)
          ·
            refine ⟨9027806944625575036891895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018537963083716691261263 9027806944625575036891895)
            ·
              refine ⟨13541710416938362555337843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9027806944625575036891895 13541710416938362555337843)
              ·
                refine ⟨20312565625407543833006765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13541710416938362555337843 20312565625407543833006765)
                ·
                  refine ⟨7617212109527828937377537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20312565625407543833006765 7617212109527828937377537)
                  ·
                    refine ⟨5712909082145871703033153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7617212109527828937377537 5712909082145871703033153)
                    ·
                      refine ⟨4284681811609403777274865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5712909082145871703033153 4284681811609403777274865)
                      ·
                        rfl

theorem cell23_8344388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_8344388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344388 prefixEnd_8344388 := by exact prefixLift 8344388
  have htrace : WordTrace (prefixWord ++ tailWord_8344388) baseStart_8344388 baseEnd_8344388 := by
    simpa [prefixWord, tailWord_8344388, baseEnd_8344388] using wordTrace_append hprefix tailTrace_8344388
  have hstable : (prefixWord ++ tailWord_8344388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344388).length < 2 ^ (prefixWord ++ tailWord_8344388).sum := by decide
  have hdescent : baseEnd_8344388 < baseStart_8344388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344416 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 9]
def baseStart_8344416 : Nat := 118140960795 + 8344416 * 2 ^ 59
def prefixEnd_8344416 : Nat := 4983230072969 + 3 ^ 40 * 8344416 * 2
def baseEnd_8344416 : Nat := 476077354340858851969415

theorem tailTrace_8344416 : CollatzResearch.WordTrace tailWord_8344416 prefixEnd_8344416 476077354340858851969415 := by
  unfold tailWord_8344416
  simp only [CollatzResearch.WordTrace]
  refine ⟨152172927268806709819442551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202897236358408946425923401 152172927268806709819442551)
  ·
    refine ⟨228259390903210064729163827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152172927268806709819442551 228259390903210064729163827)
    ·
      refine ⟨342389086354815097093745741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228259390903210064729163827 342389086354815097093745741)
      ·
        refine ⟨128395907383055661410154653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342389086354815097093745741 128395907383055661410154653)
        ·
          refine ⟨48148465268645873028807995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128395907383055661410154653 48148465268645873028807995)
          ·
            refine ⟨72222697902968809543211993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48148465268645873028807995 72222697902968809543211993)
            ·
              refine ⟨54167023427226607157408995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72222697902968809543211993 54167023427226607157408995)
              ·
                refine ⟨81250535140839910736113493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54167023427226607157408995 81250535140839910736113493)
                ·
                  refine ⟨476077354340858851969415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81250535140839910736113493 476077354340858851969415)
                  ·
                    rfl

theorem cell23_8344416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 9].length) (baseStart_8344416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344416 prefixEnd_8344416 := by exact prefixLift 8344416
  have htrace : WordTrace (prefixWord ++ tailWord_8344416) baseStart_8344416 baseEnd_8344416 := by
    simpa [prefixWord, tailWord_8344416, baseEnd_8344416] using wordTrace_append hprefix tailTrace_8344416
  have hstable : (prefixWord ++ tailWord_8344416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344416).length < 2 ^ (prefixWord ++ tailWord_8344416).sum := by decide
  have hdescent : baseEnd_8344416 < baseStart_8344416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344573 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_8344573 : Nat := 118140960795 + 8344573 * 2 ^ 59
def prefixEnd_8344573 : Nat := 4983230072969 + 3 ^ 40 * 8344573 * 2
def baseEnd_8344573 : Nat := 4284776805530485553461513

theorem tailTrace_8344573 : CollatzResearch.WordTrace tailWord_8344573 prefixEnd_8344573 4284776805530485553461513 := by
  unfold tailWord_8344573
  simp only [CollatzResearch.WordTrace]
  refine ⟨304351580798044635452350373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202901053865363090301566915 304351580798044635452350373)
  ·
    refine ⟨57065921399633369147315695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304351580798044635452350373 57065921399633369147315695)
    ·
      refine ⟨85598882099450053720973543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57065921399633369147315695 85598882099450053720973543)
      ·
        refine ⟨128398323149175080581460315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85598882099450053720973543 128398323149175080581460315)
        ·
          refine ⟨192597484723762620872190473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128398323149175080581460315 192597484723762620872190473)
          ·
            refine ⟨144448113542821965654142855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192597484723762620872190473 144448113542821965654142855)
            ·
              refine ⟨216672170314232948481214283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144448113542821965654142855 216672170314232948481214283)
              ·
                refine ⟨325008255471349422721821425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216672170314232948481214283 325008255471349422721821425)
                ·
                  refine ⟨243756191603512067041366069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325008255471349422721821425 243756191603512067041366069)
                  ·
                    refine ⟨22852142962829256285128069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 243756191603512067041366069 22852142962829256285128069)
                    ·
                      refine ⟨4284776805530485553461513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22852142962829256285128069 4284776805530485553461513)
                      ·
                        rfl

theorem cell23_8344573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_8344573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344573 prefixEnd_8344573 := by exact prefixLift 8344573
  have htrace : WordTrace (prefixWord ++ tailWord_8344573) baseStart_8344573 baseEnd_8344573 := by
    simpa [prefixWord, tailWord_8344573, baseEnd_8344573] using wordTrace_append hprefix tailTrace_8344573
  have hstable : (prefixWord ++ tailWord_8344573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344573).length < 2 ^ (prefixWord ++ tailWord_8344573).sum := by decide
  have hdescent : baseEnd_8344573 < baseStart_8344573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344587 : List Nat := [1, 1, 1, 1, 6, 4, 1, 2, 1, 5]
def baseStart_8344587 : Nat := 118140960795 + 8344587 * 2 ^ 59
def prefixEnd_8344587 : Nat := 4983230072969 + 3 ^ 40 * 8344587 * 2
def baseEnd_8344587 : Nat := 1428261331419882832895483

theorem tailTrace_8344587 : CollatzResearch.WordTrace tailWord_8344587 prefixEnd_8344587 1428261331419882832895483 := by
  unfold tailWord_8344587
  simp only [CollatzResearch.WordTrace]
  refine ⟨304352091419993915843360015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202901394279995943895573343 304352091419993915843360015)
  ·
    refine ⟨456528137129990873765040023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304352091419993915843360015 456528137129990873765040023)
    ·
      refine ⟨684792205694986310647560035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456528137129990873765040023 684792205694986310647560035)
      ·
        refine ⟨1027188308542479465971340053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684792205694986310647560035 1027188308542479465971340053)
        ·
          refine ⟨48149451962928724967406565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1027188308542479465971340053 48149451962928724967406565)
          ·
            refine ⟨9028022243049135931388731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48149451962928724967406565 9028022243049135931388731)
            ·
              refine ⟨13542033364573703897083097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028022243049135931388731 13542033364573703897083097)
              ·
                refine ⟨10156525023430277922812323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13542033364573703897083097 10156525023430277922812323)
                ·
                  refine ⟨15234787535145416884218485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10156525023430277922812323 15234787535145416884218485)
                  ·
                    refine ⟨1428261331419882832895483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15234787535145416884218485 1428261331419882832895483)
                    ·
                      rfl

theorem cell23_8344587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 5].length) (baseStart_8344587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344587 prefixEnd_8344587 := by exact prefixLift 8344587
  have htrace : WordTrace (prefixWord ++ tailWord_8344587) baseStart_8344587 baseEnd_8344587 := by
    simpa [prefixWord, tailWord_8344587, baseEnd_8344587] using wordTrace_append hprefix tailTrace_8344587
  have hstable : (prefixWord ++ tailWord_8344587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344587).length < 2 ^ (prefixWord ++ tailWord_8344587).sum := by decide
  have hdescent : baseEnd_8344587 < baseStart_8344587 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344593 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_8344593 : Nat := 118140960795 + 8344593 * 2 ^ 59
def prefixEnd_8344593 : Nat := 4983230072969 + 3 ^ 40 * 8344593 * 2
def baseEnd_8344593 : Nat := 4284787075143575475211421

theorem tailTrace_8344593 : CollatzResearch.WordTrace tailWord_8344593 prefixEnd_8344593 4284787075143575475211421 := by
  unfold tailWord_8344593
  simp only [CollatzResearch.WordTrace]
  refine ⟨304352310257972178868078433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202901540171981452578718955 304352310257972178868078433)
  ·
    refine ⟨228264232693479134151058825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304352310257972178868078433 228264232693479134151058825)
    ·
      refine ⟨171198174520109350613294119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228264232693479134151058825 171198174520109350613294119)
      ·
        refine ⟨256797261780164025919941179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171198174520109350613294119 256797261780164025919941179)
        ·
          refine ⟨385195892670246038879911769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256797261780164025919941179 385195892670246038879911769)
          ·
            refine ⟨288896919502684529159933827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385195892670246038879911769 288896919502684529159933827)
            ·
              refine ⟨433345379254026793739900741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288896919502684529159933827 433345379254026793739900741)
              ·
                refine ⟨81252258610130023826231389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 433345379254026793739900741 81252258610130023826231389)
                ·
                  refine ⟨30469596978798758934836771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81252258610130023826231389 30469596978798758934836771)
                  ·
                    refine ⟨45704395468198138402255157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30469596978798758934836771 45704395468198138402255157)
                    ·
                      refine ⟨4284787075143575475211421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45704395468198138402255157 4284787075143575475211421)
                      ·
                        rfl

theorem cell23_8344593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_8344593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344593 prefixEnd_8344593 := by exact prefixLift 8344593
  have htrace : WordTrace (prefixWord ++ tailWord_8344593) baseStart_8344593 baseEnd_8344593 := by
    simpa [prefixWord, tailWord_8344593, baseEnd_8344593] using wordTrace_append hprefix tailTrace_8344593
  have hstable : (prefixWord ++ tailWord_8344593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344593).length < 2 ^ (prefixWord ++ tailWord_8344593).sum := by decide
  have hdescent : baseEnd_8344593 < baseStart_8344593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344600 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 1, 6]
def baseStart_8344600 : Nat := 118140960795 + 8344600 * 2 ^ 59
def prefixEnd_8344600 : Nat := 4983230072969 + 3 ^ 40 * 8344600 * 2
def baseEnd_8344600 : Nat := 1428263556502718982607963

theorem tailTrace_8344600 : CollatzResearch.WordTrace tailWord_8344600 prefixEnd_8344600 1428263556502718982607963 := by
  unfold tailWord_8344600
  simp only [CollatzResearch.WordTrace]
  refine ⟨152176282784473409531791627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202901710379297879375722169 152176282784473409531791627)
  ·
    refine ⟨228264424176710114297687441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152176282784473409531791627 228264424176710114297687441)
    ·
      refine ⟨171198318132532585723265581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228264424176710114297687441 171198318132532585723265581)
      ·
        refine ⟨64199369299699719646224593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171198318132532585723265581 64199369299699719646224593)
        ·
          refine ⟨48149526974774789734668445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64199369299699719646224593 48149526974774789734668445)
          ·
            refine ⟨18056072615540546150500667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48149526974774789734668445 18056072615540546150500667)
            ·
              refine ⟨27084108923310819225751001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18056072615540546150500667 27084108923310819225751001)
              ·
                refine ⟨20313081692483114419313251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27084108923310819225751001 20313081692483114419313251)
                ·
                  refine ⟨30469622538724671628969877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20313081692483114419313251 30469622538724671628969877)
                  ·
                    refine ⟨1428263556502718982607963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30469622538724671628969877 1428263556502718982607963)
                    ·
                      rfl

theorem cell23_8344600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_8344600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344600 prefixEnd_8344600 := by exact prefixLift 8344600
  have htrace : WordTrace (prefixWord ++ tailWord_8344600) baseStart_8344600 baseEnd_8344600 := by
    simpa [prefixWord, tailWord_8344600, baseEnd_8344600] using wordTrace_append hprefix tailTrace_8344600
  have hstable : (prefixWord ++ tailWord_8344600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344600).length < 2 ^ (prefixWord ++ tailWord_8344600).sum := by decide
  have hdescent : baseEnd_8344600 < baseStart_8344600 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344604 : List Nat := [2, 2, 3, 1, 4, 1, 3, 1, 1, 5]
def baseStart_8344604 : Nat := 118140960795 + 8344604 * 2 ^ 59
def prefixEnd_8344604 : Nat := 4983230072969 + 3 ^ 40 * 8344604 * 2
def baseEnd_8344604 : Nat := 1428264241143591644057957

theorem tailTrace_8344604 : CollatzResearch.WordTrace tailWord_8344604 prefixEnd_8344604 1428264241143591644057957 := by
  unfold tailWord_8344604
  simp only [CollatzResearch.WordTrace]
  refine ⟨152176355730466163873364433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202901807640621551831152577 152176355730466163873364433)
  ·
    refine ⟨114132266797849622905023325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152176355730466163873364433 114132266797849622905023325)
    ·
      refine ⟨42799600049193608589383747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114132266797849622905023325 42799600049193608589383747)
      ·
        refine ⟨64199400073790412884075621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42799600049193608589383747 64199400073790412884075621)
        ·
          refine ⟨12037387513835702415764179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64199400073790412884075621 12037387513835702415764179)
          ·
            refine ⟨18056081270753553623646269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12037387513835702415764179 18056081270753553623646269)
            ·
              refine ⟨6771030476532582608867351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18056081270753553623646269 6771030476532582608867351)
              ·
                refine ⟨10156545714798873913301027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6771030476532582608867351 10156545714798873913301027)
                ·
                  refine ⟨15234818572198310869951541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10156545714798873913301027 15234818572198310869951541)
                  ·
                    refine ⟨1428264241143591644057957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15234818572198310869951541 1428264241143591644057957)
                    ·
                      rfl

theorem cell23_8344604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_8344604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344604 prefixEnd_8344604 := by exact prefixLift 8344604
  have htrace : WordTrace (prefixWord ++ tailWord_8344604) baseStart_8344604 baseEnd_8344604 := by
    simpa [prefixWord, tailWord_8344604, baseEnd_8344604] using wordTrace_append hprefix tailTrace_8344604
  have hstable : (prefixWord ++ tailWord_8344604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344604).length < 2 ^ (prefixWord ++ tailWord_8344604).sum := by decide
  have hdescent : baseEnd_8344604 < baseStart_8344604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344637 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_8344637 : Nat := 118140960795 + 8344637 * 2 ^ 59
def prefixEnd_8344637 : Nat := 4983230072969 + 3 ^ 40 * 8344637 * 2
def baseEnd_8344637 : Nat := 4284809668292373303061219

theorem tailTrace_8344637 : CollatzResearch.WordTrace tailWord_8344637 prefixEnd_8344637 4284809668292373303061219 := by
  unfold tailWord_8344637
  simp only [CollatzResearch.WordTrace]
  refine ⟨304353915069812774382680165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202902610046541849588453443 304353915069812774382680165)
  ·
    refine ⟨57066359075589895196752531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304353915069812774382680165 57066359075589895196752531)
    ·
      refine ⟨85599538613384842795128797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57066359075589895196752531 85599538613384842795128797)
      ·
        refine ⟨32099826980019316048173299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85599538613384842795128797 32099826980019316048173299)
        ·
          refine ⟨48149740470028974072259949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32099826980019316048173299 48149740470028974072259949)
          ·
            refine ⟨18056152676260865277097481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48149740470028974072259949 18056152676260865277097481)
            ·
              refine ⟨13542114507195648957823111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18056152676260865277097481 13542114507195648957823111)
              ·
                refine ⟨20313171760793473436734667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13542114507195648957823111 20313171760793473436734667)
                ·
                  refine ⟨30469757641190210155102001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20313171760793473436734667 30469757641190210155102001)
                  ·
                    refine ⟨22852318230892657616326501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30469757641190210155102001 22852318230892657616326501)
                    ·
                      refine ⟨4284809668292373303061219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22852318230892657616326501 4284809668292373303061219)
                      ·
                        rfl

theorem cell23_8344637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_8344637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344637 prefixEnd_8344637 := by exact prefixLift 8344637
  have htrace : WordTrace (prefixWord ++ tailWord_8344637) baseStart_8344637 baseEnd_8344637 := by
    simpa [prefixWord, tailWord_8344637, baseEnd_8344637] using wordTrace_append hprefix tailTrace_8344637
  have hstable : (prefixWord ++ tailWord_8344637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344637).length < 2 ^ (prefixWord ++ tailWord_8344637).sum := by decide
  have hdescent : baseEnd_8344637 < baseStart_8344637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344641 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_8344641 : Nat := 118140960795 + 8344641 * 2 ^ 59
def prefixEnd_8344641 : Nat := 4983230072969 + 3 ^ 40 * 8344641 * 2
def baseEnd_8344641 : Nat := 4284811722214991287411201

theorem tailTrace_8344641 : CollatzResearch.WordTrace tailWord_8344641 prefixEnd_8344641 4284811722214991287411201 := by
  unfold tailWord_8344641
  simp only [CollatzResearch.WordTrace]
  refine ⟨304354060961798283065825777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202902707307865522043883851 304354060961798283065825777)
  ·
    refine ⟨228265545721348712299369333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304354060961798283065825777 228265545721348712299369333)
    ·
      refine ⟨21399894911376441778065875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228265545721348712299369333 21399894911376441778065875)
      ·
        refine ⟨32099842367064662667098813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21399894911376441778065875 32099842367064662667098813)
        ·
          refine ⟨12037440887649248500162055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32099842367064662667098813 12037440887649248500162055)
          ·
            refine ⟨18056161331473872750243083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12037440887649248500162055 18056161331473872750243083)
            ·
              refine ⟨27084241997210809125364625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18056161331473872750243083 27084241997210809125364625)
              ·
                refine ⟨20313181497908106844023469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27084241997210809125364625 20313181497908106844023469)
                ·
                  refine ⟨7617443061715540066508801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20313181497908106844023469 7617443061715540066508801)
                  ·
                    refine ⟨5713082296286655049881601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7617443061715540066508801 5713082296286655049881601)
                    ·
                      refine ⟨4284811722214991287411201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5713082296286655049881601 4284811722214991287411201)
                      ·
                        rfl

theorem cell23_8344641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_8344641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344641 prefixEnd_8344641 := by exact prefixLift 8344641
  have htrace : WordTrace (prefixWord ++ tailWord_8344641) baseStart_8344641 baseEnd_8344641 := by
    simpa [prefixWord, tailWord_8344641, baseEnd_8344641] using wordTrace_append hprefix tailTrace_8344641
  have hstable : (prefixWord ++ tailWord_8344641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344641).length < 2 ^ (prefixWord ++ tailWord_8344641).sum := by decide
  have hdescent : baseEnd_8344641 < baseStart_8344641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344643 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 2, 7]
def baseStart_8344643 : Nat := 118140960795 + 8344643 * 2 ^ 59
def prefixEnd_8344643 : Nat := 4983230072969 + 3 ^ 40 * 8344643 * 2
def baseEnd_8344643 : Nat := 1428270916392100093195397

theorem tailTrace_8344643 : CollatzResearch.WordTrace tailWord_8344643 prefixEnd_8344643 1428270916392100093195397 := by
  unfold tailWord_8344643
  simp only [CollatzResearch.WordTrace]
  refine ⟨304354133907791037407398583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202902755938527358271599055 304354133907791037407398583)
  ·
    refine ⟨456531200861686556111097875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304354133907791037407398583 456531200861686556111097875)
    ·
      refine ⟨684796801292529834166646813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456531200861686556111097875 684796801292529834166646813)
      ·
        refine ⟨256798800484698687812492555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 684796801292529834166646813 256798800484698687812492555)
        ·
          refine ⟨385198200727048031718738833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256798800484698687812492555 385198200727048031718738833)
          ·
            refine ⟨288898650545286023789054125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385198200727048031718738833 288898650545286023789054125)
            ·
              refine ⟨108336993954482258920895297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288898650545286023789054125 108336993954482258920895297)
              ·
                refine ⟨81252745465861694190671473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108336993954482258920895297 81252745465861694190671473)
                ·
                  refine ⟨60939559099396270643003605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81252745465861694190671473 60939559099396270643003605)
                  ·
                    refine ⟨1428270916392100093195397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60939559099396270643003605 1428270916392100093195397)
                    ·
                      rfl

theorem cell23_8344643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 7].length) (baseStart_8344643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344643 prefixEnd_8344643 := by exact prefixLift 8344643
  have htrace : WordTrace (prefixWord ++ tailWord_8344643) baseStart_8344643 baseEnd_8344643 := by
    simpa [prefixWord, tailWord_8344643, baseEnd_8344643] using wordTrace_append hprefix tailTrace_8344643
  have hstable : (prefixWord ++ tailWord_8344643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344643).length < 2 ^ (prefixWord ++ tailWord_8344643).sum := by decide
  have hdescent : baseEnd_8344643 < baseStart_8344643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344658 : List Nat := [3, 2, 2, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_8344658 : Nat := 118140960795 + 8344658 * 2 ^ 59
def prefixEnd_8344658 : Nat := 4983230072969 + 3 ^ 40 * 8344658 * 2
def baseEnd_8344658 : Nat := 4284820451386117720898623

theorem tailTrace_8344658 : CollatzResearch.WordTrace tailWord_8344658 prefixEnd_8344658 4284820451386117720898623 := by
  unfold tailWord_8344658
  simp only [CollatzResearch.WordTrace]
  refine ⟨76088670250684173742298657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202903120668491129979463085 76088670250684173742298657)
  ·
    refine ⟨57066502688013130306723993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76088670250684173742298657 57066502688013130306723993)
    ·
      refine ⟨42799877016009847730042995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57066502688013130306723993 42799877016009847730042995)
      ·
        refine ⟨64199815524014771595064493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42799877016009847730042995 64199815524014771595064493)
        ·
          refine ⟨24074930821505539348149185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64199815524014771595064493 24074930821505539348149185)
          ·
            refine ⟨18056198116129154511111889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24074930821505539348149185 18056198116129154511111889)
            ·
              refine ⟨13542148587096865883333917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18056198116129154511111889 13542148587096865883333917)
              ·
                refine ⟨5078305720161324706250219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13542148587096865883333917 5078305720161324706250219)
                ·
                  refine ⟨7617458580241987059375329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5078305720161324706250219 7617458580241987059375329)
                  ·
                    refine ⟨5713093935181490294531497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7617458580241987059375329 5713093935181490294531497)
                    ·
                      refine ⟨4284820451386117720898623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5713093935181490294531497 4284820451386117720898623)
                      ·
                        rfl

theorem cell23_8344658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_8344658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344658 prefixEnd_8344658 := by exact prefixLift 8344658
  have htrace : WordTrace (prefixWord ++ tailWord_8344658) baseStart_8344658 baseEnd_8344658 := by
    simpa [prefixWord, tailWord_8344658, baseEnd_8344658] using wordTrace_append hprefix tailTrace_8344658
  have hstable : (prefixWord ++ tailWord_8344658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344658).length < 2 ^ (prefixWord ++ tailWord_8344658).sum := by decide
  have hdescent : baseEnd_8344658 < baseStart_8344658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344690 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_8344690 : Nat := 118140960795 + 8344690 * 2 ^ 59
def prefixEnd_8344690 : Nat := 4983230072969 + 3 ^ 40 * 8344690 * 2
def baseEnd_8344690 : Nat := 1428278960922353865232825

theorem tailTrace_8344690 : CollatzResearch.WordTrace tailWord_8344690 prefixEnd_8344690 1428278960922353865232825 := by
  unfold tailWord_8344690
  simp only [CollatzResearch.WordTrace]
  refine ⟨76088962034655191108589881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202903898759080509622906349 76088962034655191108589881)
  ·
    refine ⟨57066721525991393331442411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76088962034655191108589881 57066721525991393331442411)
    ·
      refine ⟨85600082288987089997163617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57066721525991393331442411 85600082288987089997163617)
      ·
        refine ⟨64200061716740317497872713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85600082288987089997163617 64200061716740317497872713)
        ·
          refine ⟨48150046287555238123404535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64200061716740317497872713 48150046287555238123404535)
          ·
            refine ⟨72225069431332857185106803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48150046287555238123404535 72225069431332857185106803)
            ·
              refine ⟨108337604146999285777660205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72225069431332857185106803 108337604146999285777660205)
              ·
                refine ⟨40626601555124732166622577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108337604146999285777660205 40626601555124732166622577)
                ·
                  refine ⟨30469951166343549124966933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40626601555124732166622577 30469951166343549124966933)
                  ·
                    refine ⟨1428278960922353865232825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30469951166343549124966933 1428278960922353865232825)
                    ·
                      rfl

theorem cell23_8344690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_8344690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344690 prefixEnd_8344690 := by exact prefixLift 8344690
  have htrace : WordTrace (prefixWord ++ tailWord_8344690) baseStart_8344690 baseEnd_8344690 := by
    simpa [prefixWord, tailWord_8344690, baseEnd_8344690] using wordTrace_append hprefix tailTrace_8344690
  have hstable : (prefixWord ++ tailWord_8344690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344690).length < 2 ^ (prefixWord ++ tailWord_8344690).sum := by decide
  have hdescent : baseEnd_8344690 < baseStart_8344690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344700 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_8344700 : Nat := 118140960795 + 8344700 * 2 ^ 59
def prefixEnd_8344700 : Nat := 4983230072969 + 3 ^ 40 * 8344700 * 2
def baseEnd_8344700 : Nat := 4284842017573606556573429

theorem tailTrace_8344700 : CollatzResearch.WordTrace tailWord_8344700 prefixEnd_8344700 4284842017573606556573429 := by
  unfold tailWord_8344700
  simp only [CollatzResearch.WordTrace]
  refine ⟨152178106434292268071111777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202904141912389690761482369 152178106434292268071111777)
  ·
    refine ⟨114133579825719201053333833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152178106434292268071111777 114133579825719201053333833)
    ·
      refine ⟨85600184869289400790000375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114133579825719201053333833 85600184869289400790000375)
      ·
        refine ⟨128400277303934101185000563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85600184869289400790000375 128400277303934101185000563)
        ·
          refine ⟨192600415955901151777500845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128400277303934101185000563 192600415955901151777500845)
          ·
            refine ⟨72225155983462931916562817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192600415955901151777500845 72225155983462931916562817)
            ·
              refine ⟨54168866987597198937422113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72225155983462931916562817 54168866987597198937422113)
              ·
                refine ⟨40626650240697899203066585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54168866987597198937422113 40626650240697899203066585)
                ·
                  refine ⟨30469987680523424402299939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40626650240697899203066585 30469987680523424402299939)
                  ·
                    refine ⟨45704981520785136603449909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30469987680523424402299939 45704981520785136603449909)
                    ·
                      refine ⟨4284842017573606556573429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45704981520785136603449909 4284842017573606556573429)
                      ·
                        rfl

theorem cell23_8344700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_8344700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344700 prefixEnd_8344700 := by exact prefixLift 8344700
  have htrace : WordTrace (prefixWord ++ tailWord_8344700) baseStart_8344700 baseEnd_8344700 := by
    simpa [prefixWord, tailWord_8344700, baseEnd_8344700] using wordTrace_append hprefix tailTrace_8344700
  have hstable : (prefixWord ++ tailWord_8344700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344700).length < 2 ^ (prefixWord ++ tailWord_8344700).sum := by decide
  have hdescent : baseEnd_8344700 < baseStart_8344700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344714 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 6, 2, 2]
def baseStart_8344714 : Nat := 118140960795 + 8344714 * 2 ^ 59
def prefixEnd_8344714 : Nat := 4983230072969 + 3 ^ 40 * 8344714 * 2
def baseEnd_8344714 : Nat := 4284849206302769501798365

theorem tailTrace_8344714 : CollatzResearch.WordTrace tailWord_8344714 prefixEnd_8344714 4284849206302769501798365 := by
  unfold tailWord_8344714
  simp only [CollatzResearch.WordTrace]
  refine ⟨76089180872633454133308299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202904482327022544355488797 76089180872633454133308299)
  ·
    refine ⟨114133771308950181199962449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76089180872633454133308299 114133771308950181199962449)
    ·
      refine ⟨85600328481712635899971837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114133771308950181199962449 85600328481712635899971837)
      ·
        refine ⟨32100123180642238462489439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85600328481712635899971837 32100123180642238462489439)
        ·
          refine ⟨48150184770963357693734159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32100123180642238462489439 48150184770963357693734159)
          ·
            refine ⟨72225277156445036540601239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48150184770963357693734159 72225277156445036540601239)
            ·
              refine ⟨108337915734667554810901859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72225277156445036540601239 108337915734667554810901859)
              ·
                refine ⟨162506873602001332216352789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108337915734667554810901859 162506873602001332216352789)
                ·
                  refine ⟨7617509700093812447641537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162506873602001332216352789 7617509700093812447641537)
                  ·
                    refine ⟨5713132275070359335731153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7617509700093812447641537 5713132275070359335731153)
                    ·
                      refine ⟨4284849206302769501798365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5713132275070359335731153 4284849206302769501798365)
                      ·
                        rfl

theorem cell23_8344714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_8344714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344714 prefixEnd_8344714 := by exact prefixLift 8344714
  have htrace : WordTrace (prefixWord ++ tailWord_8344714) baseStart_8344714 baseEnd_8344714 := by
    simpa [prefixWord, tailWord_8344714, baseEnd_8344714] using wordTrace_append hprefix tailTrace_8344714
  have hstable : (prefixWord ++ tailWord_8344714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344714).length < 2 ^ (prefixWord ++ tailWord_8344714).sum := by decide
  have hdescent : baseEnd_8344714 < baseStart_8344714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344787 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 4, 4, 2]
def baseStart_8344787 : Nat := 118140960795 + 8344787 * 2 ^ 59
def prefixEnd_8344787 : Nat := 4983230072969 + 3 ^ 40 * 8344787 * 2
def baseEnd_8344787 : Nat := 4284886690390547716185529

theorem tailTrace_8344787 : CollatzResearch.WordTrace tailWord_8344787 prefixEnd_8344787 4284886690390547716185529 := by
  unfold tailWord_8344787
  simp only [CollatzResearch.WordTrace]
  refine ⟨304359386019269350000640615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202906257346179566667093743 304359386019269350000640615)
  ·
    refine ⟨456539079028904025000960923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304359386019269350000640615 456539079028904025000960923)
    ·
      refine ⟨684808618543356037501441385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456539079028904025000960923 684808618543356037501441385)
      ·
        refine ⟨513606463907517028126081039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684808618543356037501441385 513606463907517028126081039)
        ·
          refine ⟨770409695861275542189121559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513606463907517028126081039 770409695861275542189121559)
          ·
            refine ⟨1155614543791913313283682339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770409695861275542189121559 1155614543791913313283682339)
            ·
              refine ⟨1733421815687869969925523509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155614543791913313283682339 1733421815687869969925523509)
              ·
                refine ⟨162508295220737809680517829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1733421815687869969925523509 162508295220737809680517829)
                ·
                  refine ⟨30470305353888339315097093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162508295220737809680517829 30470305353888339315097093)
                  ·
                    refine ⟨5713182253854063621580705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30470305353888339315097093 5713182253854063621580705)
                    ·
                      refine ⟨4284886690390547716185529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5713182253854063621580705 4284886690390547716185529)
                      ·
                        rfl

theorem cell23_8344787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 4, 2].length) (baseStart_8344787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344787 prefixEnd_8344787 := by exact prefixLift 8344787
  have htrace : WordTrace (prefixWord ++ tailWord_8344787) baseStart_8344787 baseEnd_8344787 := by
    simpa [prefixWord, tailWord_8344787, baseEnd_8344787] using wordTrace_append hprefix tailTrace_8344787
  have hstable : (prefixWord ++ tailWord_8344787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344787).length < 2 ^ (prefixWord ++ tailWord_8344787).sum := by decide
  have hdescent : baseEnd_8344787 < baseStart_8344787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344831 : List Nat := [1, 1, 2, 2, 1, 6, 2, 3, 1, 4]
def baseStart_8344831 : Nat := 118140960795 + 8344831 * 2 ^ 59
def prefixEnd_8344831 : Nat := 4983230072969 + 3 ^ 40 * 8344831 * 2
def baseEnd_8344831 : Nat := 1428303094513115181345109

theorem tailTrace_8344831 : CollatzResearch.WordTrace tailWord_8344831 prefixEnd_8344831 1428303094513115181345109 := by
  unfold tailWord_8344831
  simp only [CollatzResearch.WordTrace]
  refine ⟨304360990831109945515242347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202907327220739963676828231 304360990831109945515242347)
  ·
    refine ⟨456541486246664918272863521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304360990831109945515242347 456541486246664918272863521)
    ·
      refine ⟨342406114684998688704647641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456541486246664918272863521 342406114684998688704647641)
      ·
        refine ⟨256804586013749016528485731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342406114684998688704647641 256804586013749016528485731)
        ·
          refine ⟨385206879020623524792728597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256804586013749016528485731 385206879020623524792728597)
          ·
            refine ⟨18056572454091727724659153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 385206879020623524792728597 18056572454091727724659153)
            ·
              refine ⟨13542429340568795793494365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18056572454091727724659153 13542429340568795793494365)
              ·
                refine ⟨5078411002713298422560387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13542429340568795793494365 5078411002713298422560387)
                ·
                  refine ⟨7617616504069947633840581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5078411002713298422560387 7617616504069947633840581)
                  ·
                    refine ⟨1428303094513115181345109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7617616504069947633840581 1428303094513115181345109)
                    ·
                      rfl

theorem cell23_8344831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 1, 4].length) (baseStart_8344831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344831 prefixEnd_8344831 := by exact prefixLift 8344831
  have htrace : WordTrace (prefixWord ++ tailWord_8344831) baseStart_8344831 baseEnd_8344831 := by
    simpa [prefixWord, tailWord_8344831, baseEnd_8344831] using wordTrace_append hprefix tailTrace_8344831
  have hstable : (prefixWord ++ tailWord_8344831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344831).length < 2 ^ (prefixWord ++ tailWord_8344831).sum := by decide
  have hdescent : baseEnd_8344831 < baseStart_8344831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344844 : List Nat := [2, 2, 1, 2, 2, 5, 1, 2, 6]
def baseStart_8344844 : Nat := 118140960795 + 8344844 * 2 ^ 59
def prefixEnd_8344844 : Nat := 4983230072969 + 3 ^ 40 * 8344844 * 2
def baseEnd_8344844 : Nat := 476101773198650443685863

theorem tailTrace_8344844 : CollatzResearch.WordTrace tailWord_8344844 prefixEnd_8344844 476101773198650443685863 := by
  unfold tailWord_8344844
  simp only [CollatzResearch.WordTrace]
  refine ⟨152180732490031424367732793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202907643320041899156977057 152180732490031424367732793)
  ·
    refine ⟨114135549367523568275799595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152180732490031424367732793 114135549367523568275799595)
    ·
      refine ⟨171203324051285352413699393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114135549367523568275799595 171203324051285352413699393)
      ·
        refine ⟨128402493038464014310274545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171203324051285352413699393 128402493038464014310274545)
        ·
          refine ⟨96301869778848010732705909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128402493038464014310274545 96301869778848010732705909)
          ·
            refine ⟨9028300291767001006191179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96301869778848010732705909 9028300291767001006191179)
            ·
              refine ⟨13542450437650501509286769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028300291767001006191179 13542450437650501509286769)
              ·
                refine ⟨10156837828237876131965077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13542450437650501509286769 10156837828237876131965077)
                ·
                  refine ⟨476101773198650443685863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10156837828237876131965077 476101773198650443685863)
                  ·
                    rfl

theorem cell23_8344844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_8344844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344844 prefixEnd_8344844 := by exact prefixLift 8344844
  have htrace : WordTrace (prefixWord ++ tailWord_8344844) baseStart_8344844 baseEnd_8344844 := by
    simpa [prefixWord, tailWord_8344844, baseEnd_8344844] using wordTrace_append hprefix tailTrace_8344844
  have hstable : (prefixWord ++ tailWord_8344844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344844).length < 2 ^ (prefixWord ++ tailWord_8344844).sum := by decide
  have hdescent : baseEnd_8344844 < baseStart_8344844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344861 : List Nat := [1, 4, 2, 3, 1, 2, 3, 1, 6]
def baseStart_8344861 : Nat := 118140960795 + 8344861 * 2 ^ 59
def prefixEnd_8344861 : Nat := 4983230072969 + 3 ^ 40 * 8344861 * 2
def baseEnd_8344861 : Nat := 476102743106553380740021

theorem tailTrace_8344861 : CollatzResearch.WordTrace tailWord_8344861 prefixEnd_8344861 476102743106553380740021 := by
  unfold tailWord_8344861
  simp only [CollatzResearch.WordTrace]
  refine ⟨304362085021001260638834437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202908056680667507092556291 304362085021001260638834437)
  ·
    refine ⟨57067890941437736369781457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304362085021001260638834437 57067890941437736369781457)
    ·
      refine ⟨42800918206078302277336093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57067890941437736369781457 42800918206078302277336093)
      ·
        refine ⟨16050344327279363354001035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42800918206078302277336093 16050344327279363354001035)
        ·
          refine ⟨24075516490919045031001553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16050344327279363354001035 24075516490919045031001553)
          ·
            refine ⟨18056637368189283773251165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24075516490919045031001553 18056637368189283773251165)
            ·
              refine ⟨6771239013070981414969187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18056637368189283773251165 6771239013070981414969187)
              ·
                refine ⟨10156858519606472122453781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6771239013070981414969187 10156858519606472122453781)
                ·
                  refine ⟨476102743106553380740021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10156858519606472122453781 476102743106553380740021)
                  ·
                    rfl

theorem cell23_8344861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_8344861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344861 prefixEnd_8344861 := by exact prefixLift 8344861
  have htrace : WordTrace (prefixWord ++ tailWord_8344861) baseStart_8344861 baseEnd_8344861 := by
    simpa [prefixWord, tailWord_8344861, baseEnd_8344861] using wordTrace_append hprefix tailTrace_8344861
  have hstable : (prefixWord ++ tailWord_8344861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344861).length < 2 ^ (prefixWord ++ tailWord_8344861).sum := by decide
  have hdescent : baseEnd_8344861 < baseStart_8344861 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344904 : List Nat := [2, 1, 3, 1, 1, 2, 1, 6, 2, 4]
def baseStart_8344904 : Nat := 118140960795 + 8344904 * 2 ^ 59
def prefixEnd_8344904 : Nat := 4983230072969 + 3 ^ 40 * 8344904 * 2
def baseEnd_8344904 : Nat := 1428315589209041252807497

theorem tailTrace_8344904 : CollatzResearch.WordTrace tailWord_8344904 prefixEnd_8344904 1428315589209041252807497 := by
  unfold tailWord_8344904
  simp only [CollatzResearch.WordTrace]
  refine ⟨152181826679922739491324883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202909102239896985988433177 152181826679922739491324883)
  ·
    refine ⟨228272740019884109236987325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152181826679922739491324883 228272740019884109236987325)
    ·
      refine ⟨85602277507456540963870247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228272740019884109236987325 85602277507456540963870247)
      ·
        refine ⟨128403416261184811445805371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85602277507456540963870247 128403416261184811445805371)
        ·
          refine ⟨192605124391777217168708057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128403416261184811445805371 192605124391777217168708057)
          ·
            refine ⟨144453843293832912876531043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192605124391777217168708057 144453843293832912876531043)
            ·
              refine ⟨216680764940749369314796565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144453843293832912876531043 216680764940749369314796565)
              ·
                refine ⟨10156910856597626686631089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 216680764940749369314796565 10156910856597626686631089)
                ·
                  refine ⟨7617683142448220014973317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10156910856597626686631089 7617683142448220014973317)
                  ·
                    refine ⟨1428315589209041252807497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7617683142448220014973317 1428315589209041252807497)
                    ·
                      rfl

theorem cell23_8344904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_8344904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344904 prefixEnd_8344904 := by exact prefixLift 8344904
  have htrace : WordTrace (prefixWord ++ tailWord_8344904) baseStart_8344904 baseEnd_8344904 := by
    simpa [prefixWord, tailWord_8344904, baseEnd_8344904] using wordTrace_append hprefix tailTrace_8344904
  have hstable : (prefixWord ++ tailWord_8344904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344904).length < 2 ^ (prefixWord ++ tailWord_8344904).sum := by decide
  have hdescent : baseEnd_8344904 < baseStart_8344904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344914 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_8344914 : Nat := 118140960795 + 8344914 * 2 ^ 59
def prefixEnd_8344914 : Nat := 4983230072969 + 3 ^ 40 * 8344914 * 2
def baseEnd_8344914 : Nat := 4284951902433668719297445

theorem tailTrace_8344914 : CollatzResearch.WordTrace tailWord_8344914 prefixEnd_8344914 4284951902433668719297445 := by
  unfold tailWord_8344914
  simp only [CollatzResearch.WordTrace]
  refine ⟨76091004522452312672628449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202909345393206167127009197 76091004522452312672628449)
  ·
    refine ⟨57068253391839234504471337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76091004522452312672628449 57068253391839234504471337)
    ·
      refine ⟨42801190043879425878353503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57068253391839234504471337 42801190043879425878353503)
      ·
        refine ⟨64201785065819138817530255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42801190043879425878353503 64201785065819138817530255)
        ·
          refine ⟨96302677598728708226295383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64201785065819138817530255 96302677598728708226295383)
          ·
            refine ⟨144454016398093062339443075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96302677598728708226295383 144454016398093062339443075)
            ·
              refine ⟨216681024597139593509164613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144454016398093062339443075 216681024597139593509164613)
              ·
                refine ⟨40627692111963673782968365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216681024597139593509164613 40627692111963673782968365)
                ·
                  refine ⟨15235384541986377668613137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40627692111963673782968365 15235384541986377668613137)
                  ·
                    refine ⟨11426538406489783251459853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15235384541986377668613137 11426538406489783251459853)
                    ·
                      refine ⟨4284951902433668719297445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11426538406489783251459853 4284951902433668719297445)
                      ·
                        rfl

theorem cell23_8344914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_8344914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344914 prefixEnd_8344914 := by exact prefixLift 8344914
  have htrace : WordTrace (prefixWord ++ tailWord_8344914) baseStart_8344914 baseEnd_8344914 := by
    simpa [prefixWord, tailWord_8344914, baseEnd_8344914] using wordTrace_append hprefix tailTrace_8344914
  have hstable : (prefixWord ++ tailWord_8344914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344914).length < 2 ^ (prefixWord ++ tailWord_8344914).sum := by decide
  have hdescent : baseEnd_8344914 < baseStart_8344914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344917 : List Nat := [1, 3, 2, 2, 3, 1, 1, 10]
def baseStart_8344917 : Nat := 118140960795 + 8344917 * 2 ^ 59
def prefixEnd_8344917 : Nat := 4983230072969 + 3 ^ 40 * 8344917 * 2
def baseEnd_8344917 : Nat := 158701979365764155835553

theorem tailTrace_8344917 : CollatzResearch.WordTrace tailWord_8344917 prefixEnd_8344917 158701979365764155835553 := by
  unfold tailWord_8344917
  simp only [CollatzResearch.WordTrace]
  refine ⟨304364127508798382202873005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202909418339198921468582003 304364127508798382202873005)
  ·
    refine ⟨114136547815799393326077377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304364127508798382202873005 114136547815799393326077377)
    ·
      refine ⟨85602410861849544994558033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114136547815799393326077377 85602410861849544994558033)
      ·
        refine ⟨64201808146387158745918525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85602410861849544994558033 64201808146387158745918525)
        ·
          refine ⟨24075678054895184529719447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64201808146387158745918525 24075678054895184529719447)
          ·
            refine ⟨36113517082342776794579171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24075678054895184529719447 36113517082342776794579171)
            ·
              refine ⟨54170275623514165191868757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36113517082342776794579171 54170275623514165191868757)
              ·
                refine ⟨158701979365764155835553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 54170275623514165191868757 158701979365764155835553)
                ·
                  rfl

theorem cell23_8344917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 10].length) (baseStart_8344917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344917 prefixEnd_8344917 := by exact prefixLift 8344917
  have htrace : WordTrace (prefixWord ++ tailWord_8344917) baseStart_8344917 baseEnd_8344917 := by
    simpa [prefixWord, tailWord_8344917, baseEnd_8344917] using wordTrace_append hprefix tailTrace_8344917
  have hstable : (prefixWord ++ tailWord_8344917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344917).length < 2 ^ (prefixWord ++ tailWord_8344917).sum := by decide
  have hdescent : baseEnd_8344917 < baseStart_8344917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344921 : List Nat := [1, 2, 1, 2, 2, 2, 6, 1, 2, 4]
def baseStart_8344921 : Nat := 118140960795 + 8344921 * 2 ^ 59
def prefixEnd_8344921 : Nat := 4983230072969 + 3 ^ 40 * 8344921 * 2
def baseEnd_8344921 : Nat := 1428318498932750063969971

theorem tailTrace_8344921 : CollatzResearch.WordTrace tailWord_8344921 prefixEnd_8344921 1428318498932750063969971 := by
  unfold tailWord_8344921
  simp only [CollatzResearch.WordTrace]
  refine ⟨304364273400783890886018617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202909515600522593924012411 304364273400783890886018617)
  ·
    refine ⟨228273205050587918164513963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304364273400783890886018617 228273205050587918164513963)
    ·
      refine ⟨342409807575881877246770945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228273205050587918164513963 342409807575881877246770945)
      ·
        refine ⟨256807355681911407935078209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342409807575881877246770945 256807355681911407935078209)
        ·
          refine ⟨192605516761433555951308657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256807355681911407935078209 192605516761433555951308657)
          ·
            refine ⟨144454137571075166963481493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192605516761433555951308657 144454137571075166963481493)
            ·
              refine ⟨6771287698644148451413195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144454137571075166963481493 6771287698644148451413195)
              ·
                refine ⟨10156931547966222677119793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6771287698644148451413195 10156931547966222677119793)
                ·
                  refine ⟨7617698660974667007839845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10156931547966222677119793 7617698660974667007839845)
                  ·
                    refine ⟨1428318498932750063969971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7617698660974667007839845 1428318498932750063969971)
                    ·
                      rfl

theorem cell23_8344921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 2, 4].length) (baseStart_8344921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344921 prefixEnd_8344921 := by exact prefixLift 8344921
  have htrace : WordTrace (prefixWord ++ tailWord_8344921) baseStart_8344921 baseEnd_8344921 := by
    simpa [prefixWord, tailWord_8344921, baseEnd_8344921] using wordTrace_append hprefix tailTrace_8344921
  have hstable : (prefixWord ++ tailWord_8344921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344921).length < 2 ^ (prefixWord ++ tailWord_8344921).sum := by decide
  have hdescent : baseEnd_8344921 < baseStart_8344921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344931 : List Nat := [1, 1, 1, 5, 2, 2, 3, 2, 1, 2, 3]
def baseStart_8344931 : Nat := 118140960795 + 8344931 * 2 ^ 59
def prefixEnd_8344931 : Nat := 4983230072969 + 3 ^ 40 * 8344931 * 2
def baseEnd_8344931 : Nat := 4284960631604795152784867

theorem tailTrace_8344931 : CollatzResearch.WordTrace tailWord_8344931 prefixEnd_8344931 4284960631604795152784867 := by
  unfold tailWord_8344931
  simp only [CollatzResearch.WordTrace]
  refine ⟨304364638130747662593882647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202909758753831775062588431 304364638130747662593882647)
  ·
    refine ⟨456546957196121493890823971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304364638130747662593882647 456546957196121493890823971)
    ·
      refine ⟨684820435794182240836235957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456546957196121493890823971 684820435794182240836235957)
      ·
        refine ⟨64201915855704585078397121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 684820435794182240836235957 64201915855704585078397121)
        ·
          refine ⟨48151436891778438808797841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64201915855704585078397121 48151436891778438808797841)
          ·
            refine ⟨36113577668833829106598381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48151436891778438808797841 36113577668833829106598381)
            ·
              refine ⟨13542591625812685914974393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36113577668833829106598381 13542591625812685914974393)
              ·
                refine ⟨10156943719359514436230795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13542591625812685914974393 10156943719359514436230795)
                ·
                  refine ⟨15235415579039271654346193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10156943719359514436230795 15235415579039271654346193)
                  ·
                    refine ⟨11426561684279453740759645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15235415579039271654346193 11426561684279453740759645)
                    ·
                      refine ⟨4284960631604795152784867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11426561684279453740759645 4284960631604795152784867)
                      ·
                        rfl

theorem cell23_8344931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_8344931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344931 prefixEnd_8344931 := by exact prefixLift 8344931
  have htrace : WordTrace (prefixWord ++ tailWord_8344931) baseStart_8344931 baseEnd_8344931 := by
    simpa [prefixWord, tailWord_8344931, baseEnd_8344931] using wordTrace_append hprefix tailTrace_8344931
  have hstable : (prefixWord ++ tailWord_8344931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344931).length < 2 ^ (prefixWord ++ tailWord_8344931).sum := by decide
  have hdescent : baseEnd_8344931 < baseStart_8344931 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344944 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 3]
def baseStart_8344944 : Nat := 118140960795 + 8344944 * 2 ^ 59
def prefixEnd_8344944 : Nat := 4983230072969 + 3 ^ 40 * 8344944 * 2
def baseEnd_8344944 : Nat := 4284967306853303601922307

theorem tailTrace_8344944 : CollatzResearch.WordTrace tailWord_8344944 prefixEnd_8344944 4284967306853303601922307 := by
  unfold tailWord_8344944
  simp only [CollatzResearch.WordTrace]
  refine ⟨152182556139850282907052943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202910074853133710542737257 152182556139850282907052943)
  ·
    refine ⟨228273834209775424360579415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152182556139850282907052943 228273834209775424360579415)
    ·
      refine ⟨342410751314663136540869123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228273834209775424360579415 342410751314663136540869123)
      ·
        refine ⟨513616126971994704811303685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342410751314663136540869123 513616126971994704811303685)
        ·
          refine ⟨96303023807249007152119441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 513616126971994704811303685 96303023807249007152119441)
          ·
            refine ⟨72227267855436755364089581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96303023807249007152119441 72227267855436755364089581)
            ·
              refine ⟨27085225445788783261533593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72227267855436755364089581 27085225445788783261533593)
              ·
                refine ⟨20313919084341587446150195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27085225445788783261533593 20313919084341587446150195)
                ·
                  refine ⟨30470878626512381169225293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20313919084341587446150195 30470878626512381169225293)
                  ·
                    refine ⟨11426579484942142938459485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30470878626512381169225293 11426579484942142938459485)
                    ·
                      refine ⟨4284967306853303601922307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11426579484942142938459485 4284967306853303601922307)
                      ·
                        rfl

theorem cell23_8344944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 3].length) (baseStart_8344944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344944 prefixEnd_8344944 := by exact prefixLift 8344944
  have htrace : WordTrace (prefixWord ++ tailWord_8344944) baseStart_8344944 baseEnd_8344944 := by
    simpa [prefixWord, tailWord_8344944, baseEnd_8344944] using wordTrace_append hprefix tailTrace_8344944
  have hstable : (prefixWord ++ tailWord_8344944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344944).length < 2 ^ (prefixWord ++ tailWord_8344944).sum := by decide
  have hdescent : baseEnd_8344944 < baseStart_8344944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344977 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 2, 6]
def baseStart_8344977 : Nat := 118140960795 + 8344977 * 2 ^ 59
def prefixEnd_8344977 : Nat := 4983230072969 + 3 ^ 40 * 8344977 * 2
def baseEnd_8344977 : Nat := 1428328083904967324269885

theorem tailTrace_8344977 : CollatzResearch.WordTrace tailWord_8344977 prefixEnd_8344977 1428328083904967324269885 := by
  unfold tailWord_8344977
  simp only [CollatzResearch.WordTrace]
  refine ⟨304366315888581012450057185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202910877259054008300038123 304366315888581012450057185)
  ·
    refine ⟨228274736916435759337542889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304366315888581012450057185 228274736916435759337542889)
    ·
      refine ⟨171206052687326819503157167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228274736916435759337542889 171206052687326819503157167)
      ·
        refine ⟨256809079030990229254735751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171206052687326819503157167 256809079030990229254735751)
        ·
          refine ⟨385213618546485343882103627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256809079030990229254735751 385213618546485343882103627)
          ·
            refine ⟨577820427819728015823155441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385213618546485343882103627 577820427819728015823155441)
            ·
              refine ⟨433365320864796011867366581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577820427819728015823155441 433365320864796011867366581)
              ·
                refine ⟨40627998831074626112565617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 433365320864796011867366581 40627998831074626112565617)
                ·
                  refine ⟨30470999123305969584424213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40627998831074626112565617 30470999123305969584424213)
                  ·
                    refine ⟨1428328083904967324269885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30470999123305969584424213 1428328083904967324269885)
                    ·
                      rfl

theorem cell23_8344977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_8344977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344977 prefixEnd_8344977 := by exact prefixLift 8344977
  have htrace : WordTrace (prefixWord ++ tailWord_8344977) baseStart_8344977 baseEnd_8344977 := by
    simpa [prefixWord, tailWord_8344977, baseEnd_8344977] using wordTrace_append hprefix tailTrace_8344977
  have hstable : (prefixWord ++ tailWord_8344977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344977).length < 2 ^ (prefixWord ++ tailWord_8344977).sum := by decide
  have hdescent : baseEnd_8344977 < baseStart_8344977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345005 : List Nat := [1, 5, 2, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_8345005 : Nat := 118140960795 + 8345005 * 2 ^ 59
def prefixEnd_8345005 : Nat := 4983230072969 + 3 ^ 40 * 8345005 * 2
def baseEnd_8345005 : Nat := 4284998629173227863259527

theorem tailTrace_8345005 : CollatzResearch.WordTrace tailWord_8345005 prefixEnd_8345005 4284998629173227863259527 := by
  unfold tailWord_8345005
  simp only [CollatzResearch.WordTrace]
  refine ⟨304367337132479573232076469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202911558088319715488050979 304367337132479573232076469)
  ·
    refine ⟨28534437856169959990507169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304367337132479573232076469 28534437856169959990507169)
    ·
      refine ⟨21400828392127469992880377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28534437856169959990507169 21400828392127469992880377)
      ·
        refine ⟨16050621294095602494660283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21400828392127469992880377 16050621294095602494660283)
        ·
          refine ⟨24075931941143403741990425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16050621294095602494660283 24075931941143403741990425)
          ·
            refine ⟨18056948955857552806492819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24075931941143403741990425 18056948955857552806492819)
            ·
              refine ⟨27085423433786329209739229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18056948955857552806492819 27085423433786329209739229)
              ·
                refine ⟨10157033787669873453652211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27085423433786329209739229 10157033787669873453652211)
                ·
                  refine ⟨15235550681504810180478317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10157033787669873453652211 15235550681504810180478317)
                  ·
                    refine ⟨5713331505564303817679369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15235550681504810180478317 5713331505564303817679369)
                    ·
                      refine ⟨4284998629173227863259527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5713331505564303817679369 4284998629173227863259527)
                      ·
                        rfl

theorem cell23_8345005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_8345005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345005 prefixEnd_8345005 := by exact prefixLift 8345005
  have htrace : WordTrace (prefixWord ++ tailWord_8345005) baseStart_8345005 baseEnd_8345005 := by
    simpa [prefixWord, tailWord_8345005, baseEnd_8345005] using wordTrace_append hprefix tailTrace_8345005
  have hstable : (prefixWord ++ tailWord_8345005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345005).length < 2 ^ (prefixWord ++ tailWord_8345005).sum := by decide
  have hdescent : baseEnd_8345005 < baseStart_8345005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345064 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_8345064 : Nat := 118140960795 + 8345064 * 2 ^ 59
def prefixEnd_8345064 : Nat := 4983230072969 + 3 ^ 40 * 8345064 * 2
def baseEnd_8345064 : Nat := 4285028924531843132421755

theorem tailTrace_8345064 : CollatzResearch.WordTrace tailWord_8345064 prefixEnd_8345064 4285028924531843132421755 := by
  unfold tailWord_8345064
  simp only [CollatzResearch.WordTrace]
  refine ⟨152184744519632913154237123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202912992692843884205649497 152184744519632913154237123)
  ·
    refine ⟨228277116779449369731355685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152184744519632913154237123 228277116779449369731355685)
    ·
      refine ⟨42801959396146756824629191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228277116779449369731355685 42801959396146756824629191)
      ·
        refine ⟨64202939094220135236943787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42801959396146756824629191 64202939094220135236943787)
        ·
          refine ⟨96304408641330202855415681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64202939094220135236943787 96304408641330202855415681)
          ·
            refine ⟨72228306480997652141561761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96304408641330202855415681 72228306480997652141561761)
            ·
              refine ⟨54171229860748239106171321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72228306480997652141561761 54171229860748239106171321)
              ·
                refine ⟨40628422395561179329628491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54171229860748239106171321 40628422395561179329628491)
                ·
                  refine ⟨60942633593341768994442737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40628422395561179329628491 60942633593341768994442737)
                  ·
                    refine ⟨45706975195006326745832053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60942633593341768994442737 45706975195006326745832053)
                    ·
                      refine ⟨4285028924531843132421755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45706975195006326745832053 4285028924531843132421755)
                      ·
                        rfl

theorem cell23_8345064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_8345064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345064 prefixEnd_8345064 := by exact prefixLift 8345064
  have htrace : WordTrace (prefixWord ++ tailWord_8345064) baseStart_8345064 baseEnd_8345064 := by
    simpa [prefixWord, tailWord_8345064, baseEnd_8345064] using wordTrace_append hprefix tailTrace_8345064
  have hstable : (prefixWord ++ tailWord_8345064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345064).length < 2 ^ (prefixWord ++ tailWord_8345064).sum := by decide
  have hdescent : baseEnd_8345064 < baseStart_8345064 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345086 : List Nat := [4, 2, 2, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_8345086 : Nat := 118140960795 + 8345086 * 2 ^ 59
def prefixEnd_8345086 : Nat := 4983230072969 + 3 ^ 40 * 8345086 * 2
def baseEnd_8345086 : Nat := 4285040221106242046346655

theorem tailTrace_8345086 : CollatzResearch.WordTrace tailWord_8345086 prefixEnd_8345086 4285040221106242046346655 := by
  unfold tailWord_8345086
  simp only [CollatzResearch.WordTrace]
  refine ⟨38046286430648265508221889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202913527630124082710516741 38046286430648265508221889)
  ·
    refine ⟨28534714822986199131166417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38046286430648265508221889 28534714822986199131166417)
    ·
      refine ⟨21401036117239649348374813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28534714822986199131166417 21401036117239649348374813)
      ·
        refine ⟨8025388543964868505640555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21401036117239649348374813 8025388543964868505640555)
        ·
          refine ⟨12038082815947302758460833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8025388543964868505640555 12038082815947302758460833)
          ·
            refine ⟨9028562111960477068845625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12038082815947302758460833 9028562111960477068845625)
            ·
              refine ⟨6771421583970357801634219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9028562111960477068845625 6771421583970357801634219)
              ·
                refine ⟨10157132375955536702451329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6771421583970357801634219 10157132375955536702451329)
                ·
                  refine ⟨7617849281966652526838497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10157132375955536702451329 7617849281966652526838497)
                  ·
                    refine ⟨5713386961474989395128873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7617849281966652526838497 5713386961474989395128873)
                    ·
                      refine ⟨4285040221106242046346655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5713386961474989395128873 4285040221106242046346655)
                      ·
                        rfl

theorem cell23_8345086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_8345086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345086 prefixEnd_8345086 := by exact prefixLift 8345086
  have htrace : WordTrace (prefixWord ++ tailWord_8345086) baseStart_8345086 baseEnd_8345086 := by
    simpa [prefixWord, tailWord_8345086, baseEnd_8345086] using wordTrace_append hprefix tailTrace_8345086
  have hstable : (prefixWord ++ tailWord_8345086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345086).length < 2 ^ (prefixWord ++ tailWord_8345086).sum := by decide
  have hdescent : baseEnd_8345086 < baseStart_8345086 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345175 : List Nat := [1, 1, 3, 2, 2, 3, 1, 5, 1, 1, 3]
def baseStart_8345175 : Nat := 118140960795 + 8345175 * 2 ^ 59
def prefixEnd_8345175 : Nat := 4983230072969 + 3 ^ 40 * 8345175 * 2
def baseEnd_8345175 : Nat := 4285085920884492198133745

theorem tailTrace_8345175 : CollatzResearch.WordTrace tailWord_8345175 prefixEnd_8345175 4285085920884492198133745 := by
  unfold tailWord_8345175
  simp only [CollatzResearch.WordTrace]
  refine ⟨304373537541863692265764979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202915691694575794843843319 304373537541863692265764979)
  ·
    refine ⟨456560306312795538398647469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304373537541863692265764979 456560306312795538398647469)
    ·
      refine ⟨171210114867298326899492801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456560306312795538398647469 171210114867298326899492801)
      ·
        refine ⟨128407586150473745174619601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171210114867298326899492801 128407586150473745174619601)
        ·
          refine ⟨96305689612855308880964701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128407586150473745174619601 96305689612855308880964701)
          ·
            refine ⟨36114633604820740830361763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96305689612855308880964701 36114633604820740830361763)
            ·
              refine ⟨54171950407231111245542645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36114633604820740830361763 54171950407231111245542645)
              ·
                refine ⟨5078620350677916679269623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54171950407231111245542645 5078620350677916679269623)
                ·
                  refine ⟨7617930526016875018904435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5078620350677916679269623 7617930526016875018904435)
                  ·
                    refine ⟨11426895789025312528356653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7617930526016875018904435 11426895789025312528356653)
                    ·
                      refine ⟨4285085920884492198133745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11426895789025312528356653 4285085920884492198133745)
                      ·
                        rfl

theorem cell23_8345175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_8345175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345175 prefixEnd_8345175 := by exact prefixLift 8345175
  have htrace : WordTrace (prefixWord ++ tailWord_8345175) baseStart_8345175 baseEnd_8345175 := by
    simpa [prefixWord, tailWord_8345175, baseEnd_8345175] using wordTrace_append hprefix tailTrace_8345175
  have hstable : (prefixWord ++ tailWord_8345175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345175).length < 2 ^ (prefixWord ++ tailWord_8345175).sum := by decide
  have hdescent : baseEnd_8345175 < baseStart_8345175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345192 : List Nat := [2, 1, 4, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_8345192 : Nat := 118140960795 + 8345192 * 2 ^ 59
def prefixEnd_8345192 : Nat := 4983230072969 + 3 ^ 40 * 8345192 * 2
def baseEnd_8345192 : Nat := 4285094650055618631621167

theorem tailTrace_8345192 : CollatzResearch.WordTrace tailWord_8345192 prefixEnd_8345192 4285094650055618631621167 := by
  unfold tailWord_8345192
  simp only [CollatzResearch.WordTrace]
  refine ⟨152187078791401052084566915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202916105055201402779422553 152187078791401052084566915)
  ·
    refine ⟨228280618187101578126850373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152187078791401052084566915 228280618187101578126850373)
    ·
      refine ⟨42802615910081545898784445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228280618187101578126850373 42802615910081545898784445)
      ·
        refine ⟨16050980966280579712044167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42802615910081545898784445 16050980966280579712044167)
        ·
          refine ⟨24076471449420869568066251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16050980966280579712044167 24076471449420869568066251)
          ·
            refine ⟨36114707174131304352099377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24076471449420869568066251 36114707174131304352099377)
            ·
              refine ⟨27086030380598478264074533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36114707174131304352099377 27086030380598478264074533)
              ·
                refine ⟨5078630696362214674513975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27086030380598478264074533 5078630696362214674513975)
                ·
                  refine ⟨7617946044543322011770963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5078630696362214674513975 7617946044543322011770963)
                  ·
                    refine ⟨11426919066814983017656445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7617946044543322011770963 11426919066814983017656445)
                    ·
                      refine ⟨4285094650055618631621167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11426919066814983017656445 4285094650055618631621167)
                      ·
                        rfl

theorem cell23_8345192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_8345192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345192 prefixEnd_8345192 := by exact prefixLift 8345192
  have htrace : WordTrace (prefixWord ++ tailWord_8345192) baseStart_8345192 baseEnd_8345192 := by
    simpa [prefixWord, tailWord_8345192, baseEnd_8345192] using wordTrace_append hprefix tailTrace_8345192
  have hstable : (prefixWord ++ tailWord_8345192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345192).length < 2 ^ (prefixWord ++ tailWord_8345192).sum := by decide
  have hdescent : baseEnd_8345192 < baseStart_8345192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345201 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 5, 2, 3]
def baseStart_8345201 : Nat := 118140960795 + 8345201 * 2 ^ 59
def prefixEnd_8345201 : Nat := 4983230072969 + 3 ^ 40 * 8345201 * 2
def baseEnd_8345201 : Nat := 4285099271381509096408625

theorem tailTrace_8345201 : CollatzResearch.WordTrace tailWord_8345201 prefixEnd_8345201 4285099271381509096408625 := by
  unfold tailWord_8345201
  simp only [CollatzResearch.WordTrace]
  refine ⟨304374485839769498706211457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202916323893179665804140971 304374485839769498706211457)
  ·
    refine ⟨228280864379827124029658593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304374485839769498706211457 228280864379827124029658593)
    ·
      refine ⟨171210648284870343022243945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228280864379827124029658593 171210648284870343022243945)
      ·
        refine ⟨128407986213652757266682959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171210648284870343022243945 128407986213652757266682959)
        ·
          refine ⟨192611979320479135900024439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128407986213652757266682959 192611979320479135900024439)
          ·
            refine ⟨288917968980718703850036659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192611979320479135900024439 288917968980718703850036659)
            ·
              refine ⟨433376953471078055775054989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288917968980718703850036659 433376953471078055775054989)
              ·
                refine ⟨162516357551654270915645621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433376953471078055775054989 162516357551654270915645621)
                ·
                  refine ⟨15235908520467587898341777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162516357551654270915645621 15235908520467587898341777)
                  ·
                    refine ⟨11426931390350690923756333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15235908520467587898341777 11426931390350690923756333)
                    ·
                      refine ⟨4285099271381509096408625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11426931390350690923756333 4285099271381509096408625)
                      ·
                        rfl

theorem cell23_8345201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_8345201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345201 prefixEnd_8345201 := by exact prefixLift 8345201
  have htrace : WordTrace (prefixWord ++ tailWord_8345201) baseStart_8345201 baseEnd_8345201 := by
    simpa [prefixWord, tailWord_8345201, baseEnd_8345201] using wordTrace_append hprefix tailTrace_8345201
  have hstable : (prefixWord ++ tailWord_8345201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345201).length < 2 ^ (prefixWord ++ tailWord_8345201).sum := by decide
  have hdescent : baseEnd_8345201 < baseStart_8345201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345269 : List Nat := [1, 3, 3, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_8345269 : Nat := 118140960795 + 8345269 * 2 ^ 59
def prefixEnd_8345269 : Nat := 4983230072969 + 3 ^ 40 * 8345269 * 2
def baseEnd_8345269 : Nat := 4285134188066014830358313

theorem tailTrace_8345269 : CollatzResearch.WordTrace tailWord_8345269 prefixEnd_8345269 4285134188066014830358313 := by
  unfold tailWord_8345269
  simp only [CollatzResearch.WordTrace]
  refine ⟨304376966003523146319686861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202917977335682097546457907 304376966003523146319686861)
  ·
    refine ⟨114141362251321179869882573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304376966003523146319686861 114141362251321179869882573)
    ·
      refine ⟨42803010844245442451205965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114141362251321179869882573 42803010844245442451205965)
      ·
        refine ⟨16051129066592040919202237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42803010844245442451205965 16051129066592040919202237)
        ·
          refine ⟨6019173399972015344700839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16051129066592040919202237 6019173399972015344700839)
          ·
            refine ⟨9028760099958023017051259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6019173399972015344700839 9028760099958023017051259)
            ·
              refine ⟨13543140149937034525576889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028760099958023017051259 13543140149937034525576889)
              ·
                refine ⟨10157355112452775894182667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13543140149937034525576889 10157355112452775894182667)
                ·
                  refine ⟨15236032668679163841274001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10157355112452775894182667 15236032668679163841274001)
                  ·
                    refine ⟨11427024501509372880955501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15236032668679163841274001 11427024501509372880955501)
                    ·
                      refine ⟨4285134188066014830358313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11427024501509372880955501 4285134188066014830358313)
                      ·
                        rfl

theorem cell23_8345269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_8345269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345269 prefixEnd_8345269 := by exact prefixLift 8345269
  have htrace : WordTrace (prefixWord ++ tailWord_8345269) baseStart_8345269 baseEnd_8345269 := by
    simpa [prefixWord, tailWord_8345269, baseEnd_8345269] using wordTrace_append hprefix tailTrace_8345269
  have hstable : (prefixWord ++ tailWord_8345269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345269).length < 2 ^ (prefixWord ++ tailWord_8345269).sum := by decide
  have hdescent : baseEnd_8345269 < baseStart_8345269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345286 : List Nat := [6, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_8345286 : Nat := 118140960795 + 8345286 * 2 ^ 59
def prefixEnd_8345286 : Nat := 4983230072969 + 3 ^ 40 * 8345286 * 2
def baseEnd_8345286 : Nat := 4285142917237141263845735

theorem tailTrace_8345286 : CollatzResearch.WordTrace tailWord_8345286 prefixEnd_8345286 4285142917237141263845735 := by
  unfold tailWord_8345286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9511799563889423694470491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202918390696307705482037141 9511799563889423694470491)
  ·
    refine ⟨14267699345834135541705737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9511799563889423694470491 14267699345834135541705737)
    ·
      refine ⟨10700774509375601656279303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14267699345834135541705737 10700774509375601656279303)
      ·
        refine ⟨16051161764063402484418955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10700774509375601656279303 16051161764063402484418955)
        ·
          refine ⟨24076742646095103726628433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16051161764063402484418955 24076742646095103726628433)
          ·
            refine ⟨18057556984571327794971325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24076742646095103726628433 18057556984571327794971325)
            ·
              refine ⟨6771583869214247923114247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18057556984571327794971325 6771583869214247923114247)
              ·
                refine ⟨10157375803821371884671371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6771583869214247923114247 10157375803821371884671371)
                ·
                  refine ⟨15236063705732057827007057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10157375803821371884671371 15236063705732057827007057)
                  ·
                    refine ⟨11427047779299043370255293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15236063705732057827007057 11427047779299043370255293)
                    ·
                      refine ⟨4285142917237141263845735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11427047779299043370255293 4285142917237141263845735)
                      ·
                        rfl

theorem cell23_8345286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_8345286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345286 prefixEnd_8345286 := by exact prefixLift 8345286
  have htrace : WordTrace (prefixWord ++ tailWord_8345286) baseStart_8345286 baseEnd_8345286 := by
    simpa [prefixWord, tailWord_8345286, baseEnd_8345286] using wordTrace_append hprefix tailTrace_8345286
  have hstable : (prefixWord ++ tailWord_8345286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345286).length < 2 ^ (prefixWord ++ tailWord_8345286).sum := by decide
  have hdescent : baseEnd_8345286 < baseStart_8345286 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345291 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 3]
def baseStart_8345291 : Nat := 118140960795 + 8345291 * 2 ^ 59
def prefixEnd_8345291 : Nat := 4983230072969 + 3 ^ 40 * 8345291 * 2
def baseEnd_8345291 : Nat := 4285145484640413744283211

theorem tailTrace_8345291 : CollatzResearch.WordTrace tailWord_8345291 prefixEnd_8345291 4285145484640413744283211 := by
  unfold tailWord_8345291
  simp only [CollatzResearch.WordTrace]
  refine ⟨304377768409443444076987727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202918512272962296051325151 304377768409443444076987727)
  ·
    refine ⟨456566652614165166115481591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304377768409443444076987727 456566652614165166115481591)
    ·
      refine ⟨684849978921247749173222387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456566652614165166115481591 684849978921247749173222387)
      ·
        refine ⟨1027274968381871623759833581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684849978921247749173222387 1027274968381871623759833581)
        ·
          refine ⟨385228113143201858909937593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1027274968381871623759833581 385228113143201858909937593)
          ·
            refine ⟨288921084857401394182453195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385228113143201858909937593 288921084857401394182453195)
            ·
              refine ⟨433381627286102091273679793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288921084857401394182453195 433381627286102091273679793)
              ·
                refine ⟨325036220464576568455259845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433381627286102091273679793 325036220464576568455259845)
                ·
                  refine ⟨60944291337108106585361221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325036220464576568455259845 60944291337108106585361221)
                  ·
                    refine ⟨11427054625707769984755229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60944291337108106585361221 11427054625707769984755229)
                    ·
                      refine ⟨4285145484640413744283211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11427054625707769984755229 4285145484640413744283211)
                      ·
                        rfl

theorem cell23_8345291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 3].length) (baseStart_8345291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345291 prefixEnd_8345291 := by exact prefixLift 8345291
  have htrace : WordTrace (prefixWord ++ tailWord_8345291) baseStart_8345291 baseEnd_8345291 := by
    simpa [prefixWord, tailWord_8345291, baseEnd_8345291] using wordTrace_append hprefix tailTrace_8345291
  have hstable : (prefixWord ++ tailWord_8345291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345291).length < 2 ^ (prefixWord ++ tailWord_8345291).sum := by decide
  have hdescent : baseEnd_8345291 < baseStart_8345291 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345311 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 7]
def baseStart_8345311 : Nat := 118140960795 + 8345311 * 2 ^ 59
def prefixEnd_8345311 : Nat := 4983230072969 + 3 ^ 40 * 8345311 * 2
def baseEnd_8345311 : Nat := 476128417139278185114791

theorem tailTrace_8345311 : CollatzResearch.WordTrace tailWord_8345311 prefixEnd_8345311 476128417139278185114791 := by
  unfold tailWord_8345311
  simp only [CollatzResearch.WordTrace]
  refine ⟨304378497869370987492715787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202918998579580658328477191 304378497869370987492715787)
  ·
    refine ⟨456567746804056481239073681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304378497869370987492715787 456567746804056481239073681)
    ·
      refine ⟨342425810103042360929305261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456567746804056481239073681 342425810103042360929305261)
      ·
        refine ⟨128409678788640885348489473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342425810103042360929305261 128409678788640885348489473)
        ·
          refine ⟨96307259091480664011367105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128409678788640885348489473 96307259091480664011367105)
          ·
            refine ⟨72230444318610498008525329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96307259091480664011367105 72230444318610498008525329)
            ·
              refine ⟨54172833238957873506393997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72230444318610498008525329 54172833238957873506393997)
              ·
                refine ⟨20314812464609202564897749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54172833238957873506393997 20314812464609202564897749)
                ·
                  refine ⟨476128417139278185114791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20314812464609202564897749 476128417139278185114791)
                  ·
                    rfl

theorem cell23_8345311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 7].length) (baseStart_8345311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345311 prefixEnd_8345311 := by exact prefixLift 8345311
  have htrace : WordTrace (prefixWord ++ tailWord_8345311) baseStart_8345311 baseEnd_8345311 := by
    simpa [prefixWord, tailWord_8345311, baseEnd_8345311] using wordTrace_append hprefix tailTrace_8345311
  have hstable : (prefixWord ++ tailWord_8345311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345311).length < 2 ^ (prefixWord ++ tailWord_8345311).sum := by decide
  have hdescent : baseEnd_8345311 < baseStart_8345311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345322 : List Nat := [3, 1, 3, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_8345322 : Nat := 118140960795 + 8345322 * 2 ^ 59
def prefixEnd_8345322 : Nat := 4983230072969 + 3 ^ 40 * 8345322 * 2
def baseEnd_8345322 : Nat := 4285161402540703122995569

theorem tailTrace_8345322 : CollatzResearch.WordTrace tailWord_8345322 prefixEnd_8345322 4285161402540703122995569 := by
  unfold tailWord_8345322
  simp only [CollatzResearch.WordTrace]
  refine ⟨76094724768082784092841555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202919266048220757580910813 76094724768082784092841555)
  ·
    refine ⟨114142087152124176139262333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76094724768082784092841555 114142087152124176139262333)
    ·
      refine ⟨42803282682046566052223375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114142087152124176139262333 42803282682046566052223375)
      ·
        refine ⟨64204924023069849078335063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42803282682046566052223375 64204924023069849078335063)
        ·
          refine ⟨96307386034604773617502595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64204924023069849078335063 96307386034604773617502595)
          ·
            refine ⟨144461079051907160426253893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96307386034604773617502595 144461079051907160426253893)
            ·
              refine ⟨27086452322232592579922605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144461079051907160426253893 27086452322232592579922605)
              ·
                refine ⟨10157419620837222217470977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27086452322232592579922605 10157419620837222217470977)
                ·
                  refine ⟨7618064715627916663103233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10157419620837222217470977 7618064715627916663103233)
                  ·
                    refine ⟨5713548536720937497327425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7618064715627916663103233 5713548536720937497327425)
                    ·
                      refine ⟨4285161402540703122995569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5713548536720937497327425 4285161402540703122995569)
                      ·
                        rfl

theorem cell23_8345322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_8345322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345322 prefixEnd_8345322 := by exact prefixLift 8345322
  have htrace : WordTrace (prefixWord ++ tailWord_8345322) baseStart_8345322 baseEnd_8345322 := by
    simpa [prefixWord, tailWord_8345322, baseEnd_8345322] using wordTrace_append hprefix tailTrace_8345322
  have hstable : (prefixWord ++ tailWord_8345322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345322).length < 2 ^ (prefixWord ++ tailWord_8345322).sum := by decide
  have hdescent : baseEnd_8345322 < baseStart_8345322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345358 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_8345358 : Nat := 118140960795 + 8345358 * 2 ^ 59
def prefixEnd_8345358 : Nat := 4983230072969 + 3 ^ 40 * 8345358 * 2
def baseEnd_8345358 : Nat := 1428393295948088327381801

theorem tailTrace_8345358 : CollatzResearch.WordTrace tailWord_8345358 prefixEnd_8345358 1428393295948088327381801 := by
  unfold tailWord_8345358
  simp only [CollatzResearch.WordTrace]
  refine ⟨38047526512525089314959591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202920141400133809679784485 38047526512525089314959591)
  ·
    refine ⟨57071289768787633972439387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38047526512525089314959591 57071289768787633972439387)
    ·
      refine ⟨85606934653181450958659081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57071289768787633972439387 85606934653181450958659081)
      ·
        refine ⟨64205200989886088218994311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85606934653181450958659081 64205200989886088218994311)
        ·
          refine ⟨96307801484829132328491467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64205200989886088218994311 96307801484829132328491467)
          ·
            refine ⟨144461702227243698492737201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96307801484829132328491467 144461702227243698492737201)
            ·
              refine ⟨108346276670432773869552901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144461702227243698492737201 108346276670432773869552901)
              ·
                refine ⟨20314926875706145100541169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108346276670432773869552901 20314926875706145100541169)
                ·
                  refine ⟨15236195156779608825405877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20314926875706145100541169 15236195156779608825405877)
                  ·
                    refine ⟨1428393295948088327381801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15236195156779608825405877 1428393295948088327381801)
                    ·
                      rfl

theorem cell23_8345358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_8345358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345358 prefixEnd_8345358 := by exact prefixLift 8345358
  have htrace : WordTrace (prefixWord ++ tailWord_8345358) baseStart_8345358 baseEnd_8345358 := by
    simpa [prefixWord, tailWord_8345358, baseEnd_8345358] using wordTrace_append hprefix tailTrace_8345358
  have hstable : (prefixWord ++ tailWord_8345358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345358).length < 2 ^ (prefixWord ++ tailWord_8345358).sum := by decide
  have hdescent : baseEnd_8345358 < baseStart_8345358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345362 : List Nat := [3, 2, 4, 1, 1, 1, 2, 4, 5]
def baseStart_8345362 : Nat := 118140960795 + 8345362 * 2 ^ 59
def prefixEnd_8345362 : Nat := 4983230072969 + 3 ^ 40 * 8345362 * 2
def baseEnd_8345362 : Nat := 476131326862986996277265

theorem tailTrace_8345362 : CollatzResearch.WordTrace tailWord_8345362 prefixEnd_8345362 476131326862986996277265 := by
  unfold tailWord_8345362
  simp only [CollatzResearch.WordTrace]
  refine ⟨76095089498046555800705585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202920238661457482135214893 76095089498046555800705585)
  ·
    refine ⟨57071317123534916850529189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76095089498046555800705585 57071317123534916850529189)
    ·
      refine ⟨10700871960662796909474223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57071317123534916850529189 10700871960662796909474223)
      ·
        refine ⟨16051307940994195364211335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10700871960662796909474223 16051307940994195364211335)
        ·
          refine ⟨24076961911491293046317003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16051307940994195364211335 24076961911491293046317003)
          ·
            refine ⟨36115442867236939569475505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24076961911491293046317003 36115442867236939569475505)
            ·
              refine ⟨27086582150427704677106629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36115442867236939569475505 27086582150427704677106629)
              ·
                refine ⟨5078734153205194626957493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27086582150427704677106629 5078734153205194626957493)
                ·
                  refine ⟨476131326862986996277265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5078734153205194626957493 476131326862986996277265)
                  ·
                    rfl

theorem cell23_8345362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_8345362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345362 prefixEnd_8345362 := by exact prefixLift 8345362
  have htrace : WordTrace (prefixWord ++ tailWord_8345362) baseStart_8345362 baseEnd_8345362 := by
    simpa [prefixWord, tailWord_8345362, baseEnd_8345362] using wordTrace_append hprefix tailTrace_8345362
  have hstable : (prefixWord ++ tailWord_8345362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345362).length < 2 ^ (prefixWord ++ tailWord_8345362).sum := by decide
  have hdescent : baseEnd_8345362 < baseStart_8345362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345378 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_8345378 : Nat := 118140960795 + 8345378 * 2 ^ 59
def prefixEnd_8345378 : Nat := 4983230072969 + 3 ^ 40 * 8345378 * 2
def baseEnd_8345378 : Nat := 4285190157457354903895311

theorem tailTrace_8345378 : CollatzResearch.WordTrace tailWord_8345378 prefixEnd_8345378 4285190157457354903895311 := by
  unfold tailWord_8345378
  simp only [CollatzResearch.WordTrace]
  refine ⟨76095235390032064483851197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202920627706752171956936525 76095235390032064483851197)
  ·
    refine ⟨28535713271262024181444199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76095235390032064483851197 28535713271262024181444199)
    ·
      refine ⟨42803569906893036272166299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28535713271262024181444199 42803569906893036272166299)
      ·
        refine ⟨64205354860339554408249449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42803569906893036272166299 64205354860339554408249449)
        ·
          refine ⟨48154016145254665806187087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64205354860339554408249449 48154016145254665806187087)
          ·
            refine ⟨72231024217881998709280631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48154016145254665806187087 72231024217881998709280631)
            ·
              refine ⟨108346536326822998063920947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72231024217881998709280631 108346536326822998063920947)
              ·
                refine ⟨162519804490234497095881421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108346536326822998063920947 162519804490234497095881421)
                ·
                  refine ⟨60944926683837936410955533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162519804490234497095881421 60944926683837936410955533)
                  ·
                    refine ⟨22854347506439226154108325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60944926683837936410955533 22854347506439226154108325)
                    ·
                      refine ⟨4285190157457354903895311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22854347506439226154108325 4285190157457354903895311)
                      ·
                        rfl

theorem cell23_8345378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_8345378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345378 prefixEnd_8345378 := by exact prefixLift 8345378
  have htrace : WordTrace (prefixWord ++ tailWord_8345378) baseStart_8345378 baseEnd_8345378 := by
    simpa [prefixWord, tailWord_8345378, baseEnd_8345378] using wordTrace_append hprefix tailTrace_8345378
  have hstable : (prefixWord ++ tailWord_8345378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345378).length < 2 ^ (prefixWord ++ tailWord_8345378).sum := by decide
  have hdescent : baseEnd_8345378 < baseStart_8345378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345391 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 6]
def baseStart_8345391 : Nat := 118140960795 + 8345391 * 2 ^ 59
def prefixEnd_8345391 : Nat := 4983230072969 + 3 ^ 40 * 8345391 * 2
def baseEnd_8345391 : Nat := 4285196832705863353032751

theorem tailTrace_8345391 : CollatzResearch.WordTrace tailWord_8345391 prefixEnd_8345391 4285196832705863353032751 := by
  unfold tailWord_8345391
  simp only [CollatzResearch.WordTrace]
  refine ⟨304381415709081161155628027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202920943806054107437085351 304381415709081161155628027)
  ·
    refine ⟨456572123563621741733442041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304381415709081161155628027 456572123563621741733442041)
    ·
      refine ⟨342429092672716306300081531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456572123563621741733442041 342429092672716306300081531)
      ·
        refine ⟨513643639009074459450122297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342429092672716306300081531 513643639009074459450122297)
        ·
          refine ⟨385232729256805844587591723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513643639009074459450122297 385232729256805844587591723)
          ·
            refine ⟨577849093885208766881387585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385232729256805844587591723 577849093885208766881387585)
            ·
              refine ⟨433386820413906575161040689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577849093885208766881387585 433386820413906575161040689)
              ·
                refine ⟨325040115310429931370780517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433386820413906575161040689 325040115310429931370780517)
                ·
                  refine ⟨60945021620705612132021347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325040115310429931370780517 60945021620705612132021347)
                  ·
                    refine ⟨91417532431058418198032021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60945021620705612132021347 91417532431058418198032021)
                    ·
                      refine ⟨4285196832705863353032751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91417532431058418198032021 4285196832705863353032751)
                      ·
                        rfl

theorem cell23_8345391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_8345391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345391 prefixEnd_8345391 := by exact prefixLift 8345391
  have htrace : WordTrace (prefixWord ++ tailWord_8345391) baseStart_8345391 baseEnd_8345391 := by
    simpa [prefixWord, tailWord_8345391, baseEnd_8345391] using wordTrace_append hprefix tailTrace_8345391
  have hstable : (prefixWord ++ tailWord_8345391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345391).length < 2 ^ (prefixWord ++ tailWord_8345391).sum := by decide
  have hdescent : baseEnd_8345391 < baseStart_8345391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345418 : List Nat := [3, 1, 2, 1, 1, 1, 4, 4, 6]
def baseStart_8345418 : Nat := 118140960795 + 8345418 * 2 ^ 59
def prefixEnd_8345418 : Nat := 4983230072969 + 3 ^ 40 * 8345418 * 2
def baseEnd_8345418 : Nat := 476134521853726083043903

theorem tailTrace_8345418 : CollatzResearch.WordTrace tailWord_8345418 prefixEnd_8345418 476134521853726083043903 := by
  unfold tailWord_8345418
  simp only [CollatzResearch.WordTrace]
  refine ⟨76095600119995836191715227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202921600319988896511240605 76095600119995836191715227)
  ·
    refine ⟨114143400179993754287572841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76095600119995836191715227 114143400179993754287572841)
    ·
      refine ⟨85607550134995315715679631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114143400179993754287572841 85607550134995315715679631)
      ·
        refine ⟨128411325202492973573519447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85607550134995315715679631 128411325202492973573519447)
        ·
          refine ⟨192616987803739460360279171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128411325202492973573519447 192616987803739460360279171)
          ·
            refine ⟨288925481705609190540418757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192616987803739460360279171 288925481705609190540418757)
            ·
              refine ⟨54173527819801723226328517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288925481705609190540418757 54173527819801723226328517)
              ·
                refine ⟨10157536466212823104936597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54173527819801723226328517 10157536466212823104936597)
                ·
                  refine ⟨476134521853726083043903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10157536466212823104936597 476134521853726083043903)
                  ·
                    rfl

theorem cell23_8345418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_8345418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345418 prefixEnd_8345418 := by exact prefixLift 8345418
  have htrace : WordTrace (prefixWord ++ tailWord_8345418) baseStart_8345418 baseEnd_8345418 := by
    simpa [prefixWord, tailWord_8345418, baseEnd_8345418] using wordTrace_append hprefix tailTrace_8345418
  have hstable : (prefixWord ++ tailWord_8345418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345418).length < 2 ^ (prefixWord ++ tailWord_8345418).sum := by decide
  have hdescent : baseEnd_8345418 < baseStart_8345418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345445 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 5, 1, 3]
def baseStart_8345445 : Nat := 118140960795 + 8345445 * 2 ^ 59
def prefixEnd_8345445 : Nat := 4983230072969 + 3 ^ 40 * 8345445 * 2
def baseEnd_8345445 : Nat := 4285224560661206141757503

theorem tailTrace_8345445 : CollatzResearch.WordTrace tailWord_8345445 prefixEnd_8345445 4285224560661206141757503 := by
  unfold tailWord_8345445
  simp only [CollatzResearch.WordTrace]
  refine ⟨304383385250885528378093789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202922256833923685585395859 304383385250885528378093789)
  ·
    refine ⟨114143769469082073141785171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304383385250885528378093789 114143769469082073141785171)
    ·
      refine ⟨171215654203623109712677757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114143769469082073141785171 171215654203623109712677757)
      ·
        refine ⟨64205870326358666142254159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171215654203623109712677757 64205870326358666142254159)
        ·
          refine ⟨96308805489537999213381239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64205870326358666142254159 96308805489537999213381239)
          ·
            refine ⟨144463208234306998820071859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96308805489537999213381239 144463208234306998820071859)
            ·
              refine ⟨216694812351460498230107789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144463208234306998820071859 216694812351460498230107789)
              ·
                refine ⟨81260554631797686836290421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216694812351460498230107789 81260554631797686836290421)
                ·
                  refine ⟨7618176996731033140902227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81260554631797686836290421 7618176996731033140902227)
                  ·
                    refine ⟨11427265495096549711353341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7618176996731033140902227 11427265495096549711353341)
                    ·
                      refine ⟨4285224560661206141757503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11427265495096549711353341 4285224560661206141757503)
                      ·
                        rfl

theorem cell23_8345445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_8345445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345445 prefixEnd_8345445 := by exact prefixLift 8345445
  have htrace : WordTrace (prefixWord ++ tailWord_8345445) baseStart_8345445 baseEnd_8345445 := by
    simpa [prefixWord, tailWord_8345445, baseEnd_8345445] using wordTrace_append hprefix tailTrace_8345445
  have hstable : (prefixWord ++ tailWord_8345445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345445).length < 2 ^ (prefixWord ++ tailWord_8345445).sum := by decide
  have hdescent : baseEnd_8345445 < baseStart_8345445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345473 : List Nat := [1, 2, 4, 4, 1, 2, 2, 2, 1, 4]
def baseStart_8345473 : Nat := 118140960795 + 8345473 * 2 ^ 59
def prefixEnd_8345473 : Nat := 4983230072969 + 3 ^ 40 * 8345473 * 2
def baseEnd_8345473 : Nat := 1428412979373177344069125

theorem tailTrace_8345473 : CollatzResearch.WordTrace tailWord_8345473 prefixEnd_8345473 1428412979373177344069125 := by
  unfold tailWord_8345473
  simp only [CollatzResearch.WordTrace]
  refine ⟨304384406494784089160113073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202922937663189392773408715 304384406494784089160113073)
  ·
    refine ⟨228288304871088066870084805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304384406494784089160113073 228288304871088066870084805)
    ·
      refine ⟨42804057163329012538140901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228288304871088066870084805 42804057163329012538140901)
      ·
        refine ⟨8025760718124189850901419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42804057163329012538140901 8025760718124189850901419)
        ·
          refine ⟨12038641077186284776352129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8025760718124189850901419 12038641077186284776352129)
          ·
            refine ⟨9028980807889713582264097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12038641077186284776352129 9028980807889713582264097)
            ·
              refine ⟨6771735605917285186698073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9028980807889713582264097 6771735605917285186698073)
              ·
                refine ⟨5078801704437963890023555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6771735605917285186698073 5078801704437963890023555)
                ·
                  refine ⟨7618202556656945835035333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5078801704437963890023555 7618202556656945835035333)
                  ·
                    refine ⟨1428412979373177344069125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7618202556656945835035333 1428412979373177344069125)
                    ·
                      rfl

theorem cell23_8345473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_8345473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345473 prefixEnd_8345473 := by exact prefixLift 8345473
  have htrace : WordTrace (prefixWord ++ tailWord_8345473) baseStart_8345473 baseEnd_8345473 := by
    simpa [prefixWord, tailWord_8345473, baseEnd_8345473] using wordTrace_append hprefix tailTrace_8345473
  have hstable : (prefixWord ++ tailWord_8345473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345473).length < 2 ^ (prefixWord ++ tailWord_8345473).sum := by decide
  have hdescent : baseEnd_8345473 < baseStart_8345473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345488 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 3]
def baseStart_8345488 : Nat := 118140960795 + 8345488 * 2 ^ 59
def prefixEnd_8345488 : Nat := 4983230072969 + 3 ^ 40 * 8345488 * 2
def baseEnd_8345488 : Nat := 4285246640329349473519805

theorem tailTrace_8345488 : CollatzResearch.WordTrace tailWord_8345488 prefixEnd_8345488 4285246640329349473519805 := by
  unfold tailWord_8345488
  simp only [CollatzResearch.WordTrace]
  refine ⟨152192476794864873360954559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202923302393153164481272745 152192476794864873360954559)
  ·
    refine ⟨228288715192297310041431839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152192476794864873360954559 228288715192297310041431839)
    ·
      refine ⟨342433072788445965062147759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228288715192297310041431839 342433072788445965062147759)
      ·
        refine ⟨513649609182668947593221639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342433072788445965062147759 513649609182668947593221639)
        ·
          refine ⟨770474413774003421389832459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513649609182668947593221639 770474413774003421389832459)
          ·
            refine ⟨1155711620661005132084748689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770474413774003421389832459 1155711620661005132084748689)
            ·
              refine ⟨866783715495753849063561517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1155711620661005132084748689 866783715495753849063561517)
              ·
                refine ⟨325043893310907693398835569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 866783715495753849063561517 325043893310907693398835569)
                ·
                  refine ⟨243782919983180770049126677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325043893310907693398835569 243782919983180770049126677)
                  ·
                    refine ⟨11427324374211598596052813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 243782919983180770049126677 11427324374211598596052813)
                    ·
                      refine ⟨4285246640329349473519805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11427324374211598596052813 4285246640329349473519805)
                      ·
                        rfl

theorem cell23_8345488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 3].length) (baseStart_8345488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345488 prefixEnd_8345488 := by exact prefixLift 8345488
  have htrace : WordTrace (prefixWord ++ tailWord_8345488) baseStart_8345488 baseEnd_8345488 := by
    simpa [prefixWord, tailWord_8345488, baseEnd_8345488] using wordTrace_append hprefix tailTrace_8345488
  have hstable : (prefixWord ++ tailWord_8345488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345488).length < 2 ^ (prefixWord ++ tailWord_8345488).sum := by decide
  have hdescent : baseEnd_8345488 < baseStart_8345488 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345495 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 1, 6]
def baseStart_8345495 : Nat := 118140960795 + 8345495 * 2 ^ 59
def prefixEnd_8345495 : Nat := 4983230072969 + 3 ^ 40 * 8345495 * 2
def baseEnd_8345495 : Nat := 1428416744897976982044091

theorem tailTrace_8345495 : CollatzResearch.WordTrace tailWord_8345495 prefixEnd_8345495 1428416744897976982044091 := by
  unfold tailWord_8345495
  simp only [CollatzResearch.WordTrace]
  refine ⟨304385208900704386917413939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202923472600469591278275959 304385208900704386917413939)
  ·
    refine ⟨456577813351056580376120909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304385208900704386917413939 456577813351056580376120909)
    ·
      refine ⟨171216680006646217641045341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456577813351056580376120909 171216680006646217641045341)
      ·
        refine ⟨64206255002492331615392003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171216680006646217641045341 64206255002492331615392003)
        ·
          refine ⟨96309382503738497423088005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64206255002492331615392003 96309382503738497423088005)
          ·
            refine ⟨18058009219450968266829001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96309382503738497423088005 18058009219450968266829001)
            ·
              refine ⟨13543506914588226200121751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18058009219450968266829001 13543506914588226200121751)
              ·
                refine ⟨20315260371882339300182627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13543506914588226200121751 20315260371882339300182627)
                ·
                  refine ⟨30472890557823508950273941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20315260371882339300182627 30472890557823508950273941)
                  ·
                    refine ⟨1428416744897976982044091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30472890557823508950273941 1428416744897976982044091)
                    ·
                      rfl

theorem cell23_8345495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_8345495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345495 prefixEnd_8345495 := by exact prefixLift 8345495
  have htrace : WordTrace (prefixWord ++ tailWord_8345495) baseStart_8345495 baseEnd_8345495 := by
    simpa [prefixWord, tailWord_8345495, baseEnd_8345495] using wordTrace_append hprefix tailTrace_8345495
  have hstable : (prefixWord ++ tailWord_8345495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345495).length < 2 ^ (prefixWord ++ tailWord_8345495).sum := by decide
  have hdescent : baseEnd_8345495 < baseStart_8345495 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345506 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_8345506 : Nat := 118140960795 + 8345506 * 2 ^ 59
def prefixEnd_8345506 : Nat := 4983230072969 + 3 ^ 40 * 8345506 * 2
def baseEnd_8345506 : Nat := 4285255882981130403094723

theorem tailTrace_8345506 : CollatzResearch.WordTrace tailWord_8345506 prefixEnd_8345506 4285255882981130403094723 := by
  unfold tailWord_8345506
  simp only [CollatzResearch.WordTrace]
  refine ⟨76096402525916133949016093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202923740069109690530709581 76096402525916133949016093)
  ·
    refine ⟨28536150947218550230881035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76096402525916133949016093 28536150947218550230881035)
    ·
      refine ⟨42804226420827825346321553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28536150947218550230881035 42804226420827825346321553)
      ·
        refine ⟨32103169815620869009741165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42804226420827825346321553 32103169815620869009741165)
        ·
          refine ⟨12038688680857825878652937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32103169815620869009741165 12038688680857825878652937)
          ·
            refine ⟨9029016510643369408989703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12038688680857825878652937 9029016510643369408989703)
            ·
              refine ⟨13543524765965054113484555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9029016510643369408989703 13543524765965054113484555)
              ·
                refine ⟨20315287148947581170226833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13543524765965054113484555 20315287148947581170226833)
                ·
                  refine ⟨15236465361710685877670125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20315287148947581170226833 15236465361710685877670125)
                  ·
                    refine ⟨5713674510641507204126297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15236465361710685877670125 5713674510641507204126297)
                    ·
                      refine ⟨4285255882981130403094723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5713674510641507204126297 4285255882981130403094723)
                      ·
                        rfl

theorem cell23_8345506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_8345506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345506 prefixEnd_8345506 := by exact prefixLift 8345506
  have htrace : WordTrace (prefixWord ++ tailWord_8345506) baseStart_8345506 baseEnd_8345506 := by
    simpa [prefixWord, tailWord_8345506, baseEnd_8345506] using wordTrace_append hprefix tailTrace_8345506
  have hstable : (prefixWord ++ tailWord_8345506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345506).length < 2 ^ (prefixWord ++ tailWord_8345506).sum := by decide
  have hdescent : baseEnd_8345506 < baseStart_8345506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345552 : List Nat := [2, 1, 1, 1, 1, 2, 4, 5, 2, 1, 3]
def baseStart_8345552 : Nat := 118140960795 + 8345552 * 2 ^ 59
def prefixEnd_8345552 : Nat := 4983230072969 + 3 ^ 40 * 8345552 * 2
def baseEnd_8345552 : Nat := 4285279503091237223119511

theorem tailTrace_8345552 : CollatzResearch.WordTrace tailWord_8345552 prefixEnd_8345552 4285279503091237223119511 := by
  unfold tailWord_8345552
  simp only [CollatzResearch.WordTrace]
  refine ⟨152193643930748942826119455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202924858574331923768159273 152193643930748942826119455)
  ·
    refine ⟨228290465896123414239179183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152193643930748942826119455 228290465896123414239179183)
    ·
      refine ⟨342435698844185121358768775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228290465896123414239179183 342435698844185121358768775)
      ·
        refine ⟨513653548266277682038153163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342435698844185121358768775 513653548266277682038153163)
        ·
          refine ⟨770480322399416523057229745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513653548266277682038153163 770480322399416523057229745)
          ·
            refine ⟨577860241799562392292922309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770480322399416523057229745 577860241799562392292922309)
            ·
              refine ⟨108348795337417948554922933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 577860241799562392292922309 108348795337417948554922933)
              ·
                refine ⟨10157699562882932677024025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108348795337417948554922933 10157699562882932677024025)
                ·
                  refine ⟨7618274672162199507768019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10157699562882932677024025 7618274672162199507768019)
                  ·
                    refine ⟨11427412008243299261652029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7618274672162199507768019 11427412008243299261652029)
                    ·
                      refine ⟨4285279503091237223119511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11427412008243299261652029 4285279503091237223119511)
                      ·
                        rfl

theorem cell23_8345552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 2, 1, 3].length) (baseStart_8345552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345552 prefixEnd_8345552 := by exact prefixLift 8345552
  have htrace : WordTrace (prefixWord ++ tailWord_8345552) baseStart_8345552 baseEnd_8345552 := by
    simpa [prefixWord, tailWord_8345552, baseEnd_8345552] using wordTrace_append hprefix tailTrace_8345552
  have hstable : (prefixWord ++ tailWord_8345552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345552).length < 2 ^ (prefixWord ++ tailWord_8345552).sum := by decide
  have hdescent : baseEnd_8345552 < baseStart_8345552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345568 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 1, 8]
def baseStart_8345568 : Nat := 118140960795 + 8345568 * 2 ^ 59
def prefixEnd_8345568 : Nat := 4983230072969 + 3 ^ 40 * 8345568 * 2
def baseEnd_8345568 : Nat := 1428429239593903053506479

theorem tailTrace_8345568 : CollatzResearch.WordTrace tailWord_8345568 prefixEnd_8345568 1428429239593903053506479 := by
  unfold tailWord_8345568
  simp only [CollatzResearch.WordTrace]
  refine ⟨152193935714719960192410679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202925247619626613589880905 152193935714719960192410679)
  ·
    refine ⟨228290903572079940288616019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152193935714719960192410679 228290903572079940288616019)
    ·
      refine ⟨342436355358119910432924029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228290903572079940288616019 342436355358119910432924029)
      ·
        refine ⟨128413633259294966412346511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342436355358119910432924029 128413633259294966412346511)
        ·
          refine ⟨192620449888942449618519767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128413633259294966412346511 192620449888942449618519767)
          ·
            refine ⟨288930674833413674427779651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192620449888942449618519767 288930674833413674427779651)
            ·
              refine ⟨433396012250120511641669477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288930674833413674427779651 433396012250120511641669477)
              ·
                refine ⟨81261752296897595932813027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 433396012250120511641669477 81261752296897595932813027)
                ·
                  refine ⟨121892628445346393899219541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81261752296897595932813027 121892628445346393899219541)
                  ·
                    refine ⟨1428429239593903053506479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121892628445346393899219541 1428429239593903053506479)
                    ·
                      rfl

theorem cell23_8345568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_8345568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345568 prefixEnd_8345568 := by exact prefixLift 8345568
  have htrace : WordTrace (prefixWord ++ tailWord_8345568) baseStart_8345568 baseEnd_8345568 := by
    simpa [prefixWord, tailWord_8345568, baseEnd_8345568] using wordTrace_append hprefix tailTrace_8345568
  have hstable : (prefixWord ++ tailWord_8345568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345568).length < 2 ^ (prefixWord ++ tailWord_8345568).sum := by decide
  have hdescent : baseEnd_8345568 < baseStart_8345568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345625 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 4, 3, 3]
def baseStart_8345625 : Nat := 118140960795 + 8345625 * 2 ^ 59
def prefixEnd_8345625 : Nat := 4983230072969 + 3 ^ 40 * 8345625 * 2
def baseEnd_8345625 : Nat := 4285316987179015437506675

theorem tailTrace_8345625 : CollatzResearch.WordTrace tailWord_8345625 prefixEnd_8345625 4285316987179015437506675 := by
  unfold tailWord_8345625
  simp only [CollatzResearch.WordTrace]
  refine ⟨304389950390233419119646329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202926633593488946079764219 304389950390233419119646329)
  ·
    refine ⟨228292462792675064339734747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304389950390233419119646329 228292462792675064339734747)
    ·
      refine ⟨342438694189012596509602121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228292462792675064339734747 342438694189012596509602121)
      ·
        refine ⟨256829020641759447382201591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342438694189012596509602121 256829020641759447382201591)
        ·
          refine ⟨385243530962639171073302387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256829020641759447382201591 385243530962639171073302387)
          ·
            refine ⟨577865296443958756609953581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385243530962639171073302387 577865296443958756609953581)
            ·
              refine ⟨216699486166484533728732593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 577865296443958756609953581 216699486166484533728732593)
              ·
                refine ⟨162524614624863400296549445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216699486166484533728732593 162524614624863400296549445)
                ·
                  refine ⟨30473365242161887555603021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162524614624863400296549445 30473365242161887555603021)
                  ·
                    refine ⟨11427511965810707833351133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30473365242161887555603021 11427511965810707833351133)
                    ·
                      refine ⟨4285316987179015437506675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11427511965810707833351133 4285316987179015437506675)
                      ·
                        rfl

theorem cell23_8345625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_8345625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345625 prefixEnd_8345625 := by exact prefixLift 8345625
  have htrace : WordTrace (prefixWord ++ tailWord_8345625) baseStart_8345625 baseEnd_8345625 := by
    simpa [prefixWord, tailWord_8345625, baseEnd_8345625] using wordTrace_append hprefix tailTrace_8345625
  have hstable : (prefixWord ++ tailWord_8345625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345625).length < 2 ^ (prefixWord ++ tailWord_8345625).sum := by decide
  have hdescent : baseEnd_8345625 < baseStart_8345625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345649 : List Nat := [1, 2, 2, 3, 1, 3, 4, 2, 5]
def baseStart_8345649 : Nat := 118140960795 + 8345649 * 2 ^ 59
def prefixEnd_8345649 : Nat := 4983230072969 + 3 ^ 40 * 8345649 * 2
def baseEnd_8345649 : Nat := 476147701190524815956285

theorem tailTrace_8345649 : CollatzResearch.WordTrace tailWord_8345649 prefixEnd_8345649 476147701190524815956285 := by
  unfold tailWord_8345649
  simp only [CollatzResearch.WordTrace]
  refine ⟨304390825742146471218520001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202927217161430980812346667 304390825742146471218520001)
  ·
    refine ⟨228293119306609853413890001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304390825742146471218520001 228293119306609853413890001)
    ·
      refine ⟨171219839479957390060417501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228293119306609853413890001 171219839479957390060417501)
      ·
        refine ⟨64207439804984021272656563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171219839479957390060417501 64207439804984021272656563)
        ·
          refine ⟨96311159707476031908984845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64207439804984021272656563 96311159707476031908984845)
          ·
            refine ⟨36116684890303511965869317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96311159707476031908984845 36116684890303511965869317)
            ·
              refine ⟨6771878416931908493600497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36116684890303511965869317 6771878416931908493600497)
              ·
                refine ⟨5078908812698931370200373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6771878416931908493600497 5078908812698931370200373)
                ·
                  refine ⟨476147701190524815956285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5078908812698931370200373 476147701190524815956285)
                  ·
                    rfl

theorem cell23_8345649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 5].length) (baseStart_8345649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345649 prefixEnd_8345649 := by exact prefixLift 8345649
  have htrace : WordTrace (prefixWord ++ tailWord_8345649) baseStart_8345649 baseEnd_8345649 := by
    simpa [prefixWord, tailWord_8345649, baseEnd_8345649] using wordTrace_append hprefix tailTrace_8345649
  have hstable : (prefixWord ++ tailWord_8345649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345649).length < 2 ^ (prefixWord ++ tailWord_8345649).sum := by decide
  have hdescent : baseEnd_8345649 < baseStart_8345649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345655 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_8345655 : Nat := 118140960795 + 8345655 * 2 ^ 59
def prefixEnd_8345655 : Nat := 4983230072969 + 3 ^ 40 * 8345655 * 2
def baseEnd_8345655 : Nat := 4285332391598650320131537

theorem tailTrace_8345655 : CollatzResearch.WordTrace tailWord_8345655 prefixEnd_8345655 4285332391598650320131537 := by
  unfold tailWord_8345655
  simp only [CollatzResearch.WordTrace]
  refine ⟨304391044580124734243238419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202927363053416489495492279 304391044580124734243238419)
  ·
    refine ⟨456586566870187101364857629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304391044580124734243238419 456586566870187101364857629)
    ·
      refine ⟨171219962576320163011821611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456586566870187101364857629 171219962576320163011821611)
      ·
        refine ⟨256829943864480244517732417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171219962576320163011821611 256829943864480244517732417)
        ·
          refine ⟨192622457898360183388299313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256829943864480244517732417 192622457898360183388299313)
          ·
            refine ⟨144466843423770137541224485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192622457898360183388299313 144466843423770137541224485)
            ·
              refine ⟨27087533141956900788979591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144466843423770137541224485 27087533141956900788979591)
              ·
                refine ⟨40631299712935351183469387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27087533141956900788979591 40631299712935351183469387)
                ·
                  refine ⟨60946949569403026775204081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40631299712935351183469387 60946949569403026775204081)
                  ·
                    refine ⟨45710212177052270081403061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60946949569403026775204081 45710212177052270081403061)
                    ·
                      refine ⟨4285332391598650320131537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45710212177052270081403061 4285332391598650320131537)
                      ·
                        rfl

theorem cell23_8345655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_8345655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345655 prefixEnd_8345655 := by exact prefixLift 8345655
  have htrace : WordTrace (prefixWord ++ tailWord_8345655) baseStart_8345655 baseEnd_8345655 := by
    simpa [prefixWord, tailWord_8345655, baseEnd_8345655] using wordTrace_append hprefix tailTrace_8345655
  have hstable : (prefixWord ++ tailWord_8345655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345655).length < 2 ^ (prefixWord ++ tailWord_8345655).sum := by decide
  have hdescent : baseEnd_8345655 < baseStart_8345655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345694 : List Nat := [4, 4, 1, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_8345694 : Nat := 118140960795 + 8345694 * 2 ^ 59
def prefixEnd_8345694 : Nat := 4983230072969 + 3 ^ 40 * 8345694 * 2
def baseEnd_8345694 : Nat := 4285352417344175667543859

theorem tailTrace_8345694 : CollatzResearch.WordTrace tailWord_8345694 prefixEnd_8345694 4285352417344175667543859 := by
  unfold tailWord_8345694
  simp only [CollatzResearch.WordTrace]
  refine ⟨38049058378372930487988517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202928311351322295935938757 38049058378372930487988517)
  ·
    refine ⟨7134198445944924466497847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38049058378372930487988517 7134198445944924466497847)
    ·
      refine ⟨10701297668917386699746771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7134198445944924466497847 10701297668917386699746771)
      ·
        refine ⟨16051946503376080049620157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10701297668917386699746771 16051946503376080049620157)
        ·
          refine ⟨6019479938766030018607559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16051946503376080049620157 6019479938766030018607559)
          ·
            refine ⟨9029219908149045027911339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6019479938766030018607559 9029219908149045027911339)
            ·
              refine ⟨13543829862223567541867009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9029219908149045027911339 13543829862223567541867009)
              ·
                refine ⟨10157872396667675656400257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13543829862223567541867009 10157872396667675656400257)
                ·
                  refine ⟨7618404297500756742300193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10157872396667675656400257 7618404297500756742300193)
                  ·
                    refine ⟨5713803223125567556725145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7618404297500756742300193 5713803223125567556725145)
                    ·
                      refine ⟨4285352417344175667543859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5713803223125567556725145 4285352417344175667543859)
                      ·
                        rfl

theorem cell23_8345694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_8345694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345694 prefixEnd_8345694 := by exact prefixLift 8345694
  have htrace : WordTrace (prefixWord ++ tailWord_8345694) baseStart_8345694 baseEnd_8345694 := by
    simpa [prefixWord, tailWord_8345694, baseEnd_8345694] using wordTrace_append hprefix tailTrace_8345694
  have hstable : (prefixWord ++ tailWord_8345694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345694).length < 2 ^ (prefixWord ++ tailWord_8345694).sum := by decide
  have hdescent : baseEnd_8345694 < baseStart_8345694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345705 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 8]
def baseStart_8345705 : Nat := 118140960795 + 8345705 * 2 ^ 59
def prefixEnd_8345705 : Nat := 4983230072969 + 3 ^ 40 * 8345705 * 2
def baseEnd_8345705 : Nat := 476150896181263902722923

theorem tailTrace_8345705 : CollatzResearch.WordTrace tailWord_8345705 prefixEnd_8345705 476150896181263902722923 := by
  unfold tailWord_8345705
  simp only [CollatzResearch.WordTrace]
  refine ⟨304392868229943592782558569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202928578819962395188372379 304392868229943592782558569)
  ·
    refine ⟨228294651172457694586918927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304392868229943592782558569 228294651172457694586918927)
    ·
      refine ⟨342441976758686541880378391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228294651172457694586918927 342441976758686541880378391)
      ·
        refine ⟨513662965138029812820567587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342441976758686541880378391 513662965138029812820567587)
        ·
          refine ⟨770494447707044719230851381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513662965138029812820567587 770494447707044719230851381)
          ·
            refine ⟨72233854472535442427892317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 770494447707044719230851381 72233854472535442427892317)
            ·
              refine ⟨27087695427200790910459619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72233854472535442427892317 27087695427200790910459619)
              ·
                refine ⟨40631543140801186365689429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27087695427200790910459619 40631543140801186365689429)
                ·
                  refine ⟨476150896181263902722923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40631543140801186365689429 476150896181263902722923)
                  ·
                    rfl

theorem cell23_8345705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 8].length) (baseStart_8345705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345705 prefixEnd_8345705 := by exact prefixLift 8345705
  have htrace : WordTrace (prefixWord ++ tailWord_8345705) baseStart_8345705 baseEnd_8345705 := by
    simpa [prefixWord, tailWord_8345705, baseEnd_8345705] using wordTrace_append hprefix tailTrace_8345705
  have hstable : (prefixWord ++ tailWord_8345705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345705).length < 2 ^ (prefixWord ++ tailWord_8345705).sum := by decide
  have hdescent : baseEnd_8345705 < baseStart_8345705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345709 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_8345709 : Nat := 118140960795 + 8345709 * 2 ^ 59
def prefixEnd_8345709 : Nat := 4983230072969 + 3 ^ 40 * 8345709 * 2
def baseEnd_8345709 : Nat := 1428453373184664369618763

theorem tailTrace_8345709 : CollatzResearch.WordTrace tailWord_8345709 prefixEnd_8345709 1428453373184664369618763 := by
  unfold tailWord_8345709
  simp only [CollatzResearch.WordTrace]
  refine ⟨304393014121929101465704181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202928676081286067643802787 304393014121929101465704181)
  ·
    refine ⟨28536845073930853262409767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304393014121929101465704181 28536845073930853262409767)
    ·
      refine ⟨42805267610896279893614651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28536845073930853262409767 42805267610896279893614651)
      ·
        refine ⟨64207901416344419840421977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42805267610896279893614651 64207901416344419840421977)
        ·
          refine ⟨48155926062258314880316483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64207901416344419840421977 48155926062258314880316483)
          ·
            refine ⟨72233889093387472320474725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48155926062258314880316483 72233889093387472320474725)
            ·
              refine ⟨13543854205010151060089011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72233889093387472320474725 13543854205010151060089011)
              ·
                refine ⟨20315781307515226590133517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13543854205010151060089011 20315781307515226590133517)
                ·
                  refine ⟨7618417990318209971300069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20315781307515226590133517 7618417990318209971300069)
                  ·
                    refine ⟨1428453373184664369618763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7618417990318209971300069 1428453373184664369618763)
                    ·
                      rfl

theorem cell23_8345709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_8345709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345709 prefixEnd_8345709 := by exact prefixLift 8345709
  have htrace : WordTrace (prefixWord ++ tailWord_8345709) baseStart_8345709 baseEnd_8345709 := by
    simpa [prefixWord, tailWord_8345709, baseEnd_8345709] using wordTrace_append hprefix tailTrace_8345709
  have hstable : (prefixWord ++ tailWord_8345709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345709).length < 2 ^ (prefixWord ++ tailWord_8345709).sum := by decide
  have hdescent : baseEnd_8345709 < baseStart_8345709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345732 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_8345732 : Nat := 118140960795 + 8345732 * 2 ^ 59
def prefixEnd_8345732 : Nat := 4983230072969 + 3 ^ 40 * 8345732 * 2
def baseEnd_8345732 : Nat := 4285371929609046518868683

theorem tailTrace_8345732 : CollatzResearch.WordTrace tailWord_8345732 prefixEnd_8345732 4285371929609046518868683 := by
  unfold tailWord_8345732
  simp only [CollatzResearch.WordTrace]
  refine ⟨152196926500422888196895725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202929235333897184262527633 152196926500422888196895725)
  ·
    refine ⟨57073847437658583073835897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152196926500422888196895725 57073847437658583073835897)
    ·
      refine ⟨42805385578243937305376923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57073847437658583073835897 42805385578243937305376923)
      ·
        refine ⟨64208078367365905958065385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42805385578243937305376923 64208078367365905958065385)
        ·
          refine ⟨48156058775524429468549039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64208078367365905958065385 48156058775524429468549039)
          ·
            refine ⟨72234088163286644202823559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48156058775524429468549039 72234088163286644202823559)
            ·
              refine ⟨108351132244929966304235339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72234088163286644202823559 108351132244929966304235339)
              ·
                refine ⟨162526698367394949456353009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108351132244929966304235339 162526698367394949456353009)
                ·
                  refine ⟨121895023775546212092264757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162526698367394949456353009 121895023775546212092264757)
                  ·
                    refine ⟨11427658478957457383649821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121895023775546212092264757 11427658478957457383649821)
                    ·
                      refine ⟨4285371929609046518868683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11427658478957457383649821 4285371929609046518868683)
                      ·
                        rfl

theorem cell23_8345732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_8345732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345732 prefixEnd_8345732 := by exact prefixLift 8345732
  have htrace : WordTrace (prefixWord ++ tailWord_8345732) baseStart_8345732 baseEnd_8345732 := by
    simpa [prefixWord, tailWord_8345732, baseEnd_8345732] using wordTrace_append hprefix tailTrace_8345732
  have hstable : (prefixWord ++ tailWord_8345732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345732).length < 2 ^ (prefixWord ++ tailWord_8345732).sum := by decide
  have hdescent : baseEnd_8345732 < baseStart_8345732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345809 : List Nat := [1, 2, 2, 1, 2, 2, 2, 5, 1, 2, 3]
def baseStart_8345809 : Nat := 118140960795 + 8345809 * 2 ^ 59
def prefixEnd_8345809 : Nat := 4983230072969 + 3 ^ 40 * 8345809 * 2
def baseEnd_8345809 : Nat := 4285411467619442717605829

theorem tailTrace_8345809 : CollatzResearch.WordTrace tailWord_8345809 prefixEnd_8345809 4285411467619442717605829 := by
  unfold tailWord_8345809
  simp only [CollatzResearch.WordTrace]
  refine ⟨304396661421566818544344481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202931107614377879029562987 304396661421566818544344481)
  ·
    refine ⟨228297496066175113908258361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304396661421566818544344481 228297496066175113908258361)
    ·
      refine ⟨171223122049631335431193771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228297496066175113908258361 171223122049631335431193771)
      ·
        refine ⟨256834683074447003146790657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171223122049631335431193771 256834683074447003146790657)
        ·
          refine ⟨192626012305835252360092993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256834683074447003146790657 192626012305835252360092993)
          ·
            refine ⟨144469509229376439270069745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192626012305835252360092993 144469509229376439270069745)
            ·
              refine ⟨108352131922032329452552309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144469509229376439270069745 108352131922032329452552309)
              ·
                refine ⟨10158012367690530886176779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108352131922032329452552309 10158012367690530886176779)
                ·
                  refine ⟨15237018551535796329265169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10158012367690530886176779 15237018551535796329265169)
                  ·
                    refine ⟨11427763913651847246948877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15237018551535796329265169 11427763913651847246948877)
                    ·
                      refine ⟨4285411467619442717605829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11427763913651847246948877 4285411467619442717605829)
                      ·
                        rfl

theorem cell23_8345809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_8345809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345809 prefixEnd_8345809 := by exact prefixLift 8345809
  have htrace : WordTrace (prefixWord ++ tailWord_8345809) baseStart_8345809 baseEnd_8345809 := by
    simpa [prefixWord, tailWord_8345809, baseEnd_8345809] using wordTrace_append hprefix tailTrace_8345809
  have hstable : (prefixWord ++ tailWord_8345809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345809).length < 2 ^ (prefixWord ++ tailWord_8345809).sum := by decide
  have hdescent : baseEnd_8345809 < baseStart_8345809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345816 : List Nat := [2, 1, 2, 2, 4, 2, 2, 2, 2, 4]
def baseStart_8345816 : Nat := 118140960795 + 8345816 * 2 ^ 59
def prefixEnd_8345816 : Nat := 4983230072969 + 3 ^ 40 * 8345816 * 2
def baseEnd_8345816 : Nat := 1428471687328008063406099

theorem tailTrace_8345816 : CollatzResearch.WordTrace tailWord_8345816 prefixEnd_8345816 1428471687328008063406099 := by
  unfold tailWord_8345816
  simp only [CollatzResearch.WordTrace]
  refine ⟨152198458366270729369924651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202931277821694305826566201 152198458366270729369924651)
  ·
    refine ⟨228297687549406094054886977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152198458366270729369924651 228297687549406094054886977)
    ·
      refine ⟨171223265662054570541165233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228297687549406094054886977 171223265662054570541165233)
      ·
        refine ⟨128417449246540927905873925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171223265662054570541165233 128417449246540927905873925)
        ·
          refine ⟨24078271733726423982351361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128417449246540927905873925 24078271733726423982351361)
          ·
            refine ⟨18058703800294817986763521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24078271733726423982351361 18058703800294817986763521)
            ·
              refine ⟨13544027850221113490072641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18058703800294817986763521 13544027850221113490072641)
              ·
                refine ⟨10158020887665835117554481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13544027850221113490072641 10158020887665835117554481)
                ·
                  refine ⟨7618515665749376338165861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10158020887665835117554481 7618515665749376338165861)
                  ·
                    refine ⟨1428471687328008063406099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7618515665749376338165861 1428471687328008063406099)
                    ·
                      rfl

theorem cell23_8345816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_8345816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345816 prefixEnd_8345816 := by exact prefixLift 8345816
  have htrace : WordTrace (prefixWord ++ tailWord_8345816) baseStart_8345816 baseEnd_8345816 := by
    simpa [prefixWord, tailWord_8345816, baseEnd_8345816] using wordTrace_append hprefix tailTrace_8345816
  have hstable : (prefixWord ++ tailWord_8345816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345816).length < 2 ^ (prefixWord ++ tailWord_8345816).sum := by decide
  have hdescent : baseEnd_8345816 < baseStart_8345816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345829 : List Nat := [1, 3, 1, 4, 2, 3, 1, 8]
def baseStart_8345829 : Nat := 118140960795 + 8345829 * 2 ^ 59
def prefixEnd_8345829 : Nat := 4983230072969 + 3 ^ 40 * 8345829 * 2
def baseEnd_8345829 : Nat := 158719323601204912568731

theorem tailTrace_8345829 : CollatzResearch.WordTrace tailWord_8345829 prefixEnd_8345829 158719323601204912568731 := by
  unfold tailWord_8345829
  simp only [CollatzResearch.WordTrace]
  refine ⟨304397390881494361960072541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202931593920996241306715027 304397390881494361960072541)
  ·
    refine ⟨114149021580560385735027203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304397390881494361960072541 114149021580560385735027203)
    ·
      refine ⟨171223532370840578602540805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114149021580560385735027203 171223532370840578602540805)
      ·
        refine ⟨32104412319532608487976401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171223532370840578602540805 32104412319532608487976401)
        ·
          refine ⟨24078309239649456365982301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32104412319532608487976401 24078309239649456365982301)
          ·
            refine ⟨9029365964868546137243363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24078309239649456365982301 9029365964868546137243363)
            ·
              refine ⟨13544048947302819205865045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9029365964868546137243363 13544048947302819205865045)
              ·
                refine ⟨158719323601204912568731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13544048947302819205865045 158719323601204912568731)
                ·
                  rfl

theorem cell23_8345829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 8].length) (baseStart_8345829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345829 prefixEnd_8345829 := by exact prefixLift 8345829
  have htrace : WordTrace (prefixWord ++ tailWord_8345829) baseStart_8345829 baseEnd_8345829 := by
    simpa [prefixWord, tailWord_8345829, baseEnd_8345829] using wordTrace_append hprefix tailTrace_8345829
  have hstable : (prefixWord ++ tailWord_8345829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345829).length < 2 ^ (prefixWord ++ tailWord_8345829).sum := by decide
  have hdescent : baseEnd_8345829 < baseStart_8345829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345839 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 3]
def baseStart_8345839 : Nat := 118140960795 + 8345839 * 2 ^ 59
def prefixEnd_8345839 : Nat := 4983230072969 + 3 ^ 40 * 8345839 * 2
def baseEnd_8345839 : Nat := 4285426872039077600230691

theorem tailTrace_8345839 : CollatzResearch.WordTrace tailWord_8345839 prefixEnd_8345839 4285426872039077600230691 := by
  unfold tailWord_8345839
  simp only [CollatzResearch.WordTrace]
  refine ⟨304397755611458133667936571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202931837074305422445291047 304397755611458133667936571)
  ·
    refine ⟨456596633417187200501904857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304397755611458133667936571 456596633417187200501904857)
    ·
      refine ⟨342447475062890400376428643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456596633417187200501904857 342447475062890400376428643)
      ·
        refine ⟨513671212594335600564642965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342447475062890400376428643 513671212594335600564642965)
        ·
          refine ⟨24078338090359481276467639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 513671212594335600564642965 24078338090359481276467639)
          ·
            refine ⟨36117507135539221914701459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24078338090359481276467639 36117507135539221914701459)
            ·
              refine ⟨54176260703308832872052189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36117507135539221914701459 54176260703308832872052189)
              ·
                refine ⟨20316097763740812327019571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54176260703308832872052189 20316097763740812327019571)
                ·
                  refine ⟨30474146645611218490529357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20316097763740812327019571 30474146645611218490529357)
                  ·
                    refine ⟨11427804992104206933948509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30474146645611218490529357 11427804992104206933948509)
                    ·
                      refine ⟨4285426872039077600230691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11427804992104206933948509 4285426872039077600230691)
                      ·
                        rfl

theorem cell23_8345839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 3].length) (baseStart_8345839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345839 prefixEnd_8345839 := by exact prefixLift 8345839
  have htrace : WordTrace (prefixWord ++ tailWord_8345839) baseStart_8345839 baseEnd_8345839 := by
    simpa [prefixWord, tailWord_8345839, baseEnd_8345839] using wordTrace_append hprefix tailTrace_8345839
  have hstable : (prefixWord ++ tailWord_8345839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345839).length < 2 ^ (prefixWord ++ tailWord_8345839).sum := by decide
  have hdescent : baseEnd_8345839 < baseStart_8345839 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345860 : List Nat := [2, 3, 2, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_8345860 : Nat := 118140960795 + 8345860 * 2 ^ 59
def prefixEnd_8345860 : Nat := 4983230072969 + 3 ^ 40 * 8345860 * 2
def baseEnd_8345860 : Nat := 4285437655132822018068095

theorem tailTrace_8345860 : CollatzResearch.WordTrace tailWord_8345860 prefixEnd_8345860 4285437655132822018068095 := by
  unfold tailWord_8345860
  simp only [CollatzResearch.WordTrace]
  refine ⟨152199260772191027127225517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202932347696254702836300689 152199260772191027127225517)
  ·
    refine ⟨57074722789571635172709569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152199260772191027127225517 57074722789571635172709569)
    ·
      refine ⟨42806042092178726379532177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57074722789571635172709569 42806042092178726379532177)
      ·
        refine ⟨32104531569134044784649133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42806042092178726379532177 32104531569134044784649133)
        ·
          refine ⟨12039199338425266794243425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32104531569134044784649133 12039199338425266794243425)
          ·
            refine ⟨9029399503818950095682569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12039199338425266794243425 9029399503818950095682569)
            ·
              refine ⟨6772049627864212571761927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9029399503818950095682569 6772049627864212571761927)
              ·
                refine ⟨10158074441796318857642891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6772049627864212571761927 10158074441796318857642891)
                ·
                  refine ⟨15237111662694478286464337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10158074441796318857642891 15237111662694478286464337)
                  ·
                    refine ⟨11427833747020858714848253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15237111662694478286464337 11427833747020858714848253)
                    ·
                      refine ⟨4285437655132822018068095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11427833747020858714848253 4285437655132822018068095)
                      ·
                        rfl

theorem cell23_8345860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_8345860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345860 prefixEnd_8345860 := by exact prefixLift 8345860
  have htrace : WordTrace (prefixWord ++ tailWord_8345860) baseStart_8345860 baseEnd_8345860 := by
    simpa [prefixWord, tailWord_8345860, baseEnd_8345860] using wordTrace_append hprefix tailTrace_8345860
  have hstable : (prefixWord ++ tailWord_8345860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345860).length < 2 ^ (prefixWord ++ tailWord_8345860).sum := by decide
  have hdescent : baseEnd_8345860 < baseStart_8345860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345873 : List Nat := [1, 2, 2, 1, 1, 7, 1, 2, 2, 1, 3]
def baseStart_8345873 : Nat := 118140960795 + 8345873 * 2 ^ 59
def prefixEnd_8345873 : Nat := 4983230072969 + 3 ^ 40 * 8345873 * 2
def baseEnd_8345873 : Nat := 4285444330381330467205535

theorem tailTrace_8345873 : CollatzResearch.WordTrace tailWord_8345873 prefixEnd_8345873 4285444330381330467205535 := by
  unfold tailWord_8345873
  simp only [CollatzResearch.WordTrace]
  refine ⟨304398995693334957474674273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202932663795556638316449515 304398995693334957474674273)
  ·
    refine ⟨228299246770001218106005705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304398995693334957474674273 228299246770001218106005705)
    ·
      refine ⟨171224435077500913579504279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228299246770001218106005705 171224435077500913579504279)
      ·
        refine ⟨256836652616251370369256419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171224435077500913579504279 256836652616251370369256419)
        ·
          refine ⟨385254978924377055553884629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256836652616251370369256419 385254978924377055553884629)
          ·
            refine ⟨9029413568540087239544171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 385254978924377055553884629 9029413568540087239544171)
            ·
              refine ⟨13544120352810130859316257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9029413568540087239544171 13544120352810130859316257)
              ·
                refine ⟨10158090264607598144487193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13544120352810130859316257 10158090264607598144487193)
                ·
                  refine ⟨7618567698455698608365395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10158090264607598144487193 7618567698455698608365395)
                  ·
                    refine ⟨11427851547683547912548093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7618567698455698608365395 11427851547683547912548093)
                    ·
                      refine ⟨4285444330381330467205535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11427851547683547912548093 4285444330381330467205535)
                      ·
                        rfl

theorem cell23_8345873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_8345873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345873 prefixEnd_8345873 := by exact prefixLift 8345873
  have htrace : WordTrace (prefixWord ++ tailWord_8345873) baseStart_8345873 baseEnd_8345873 := by
    simpa [prefixWord, tailWord_8345873, baseEnd_8345873] using wordTrace_append hprefix tailTrace_8345873
  have hstable : (prefixWord ++ tailWord_8345873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345873).length < 2 ^ (prefixWord ++ tailWord_8345873).sum := by decide
  have hdescent : baseEnd_8345873 < baseStart_8345873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345890 : List Nat := [3, 3, 1, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_8345890 : Nat := 118140960795 + 8345890 * 2 ^ 59
def prefixEnd_8345890 : Nat := 4983230072969 + 3 ^ 40 * 8345890 * 2
def baseEnd_8345890 : Nat := 4285453059552456900692957

theorem tailTrace_8345890 : CollatzResearch.WordTrace tailWord_8345890 prefixEnd_8345890 4285453059552456900692957 := by
  unfold tailWord_8345890
  simp only [CollatzResearch.WordTrace]
  refine ⟨76099903933568342344510781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202933077156182246252028749 76099903933568342344510781)
  ·
    refine ⟨28537463975088128379191543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76099903933568342344510781 28537463975088128379191543)
    ·
      refine ⟨42806195962632192568787315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28537463975088128379191543 42806195962632192568787315)
      ·
        refine ⟨64209293943948288853180973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42806195962632192568787315 64209293943948288853180973)
        ·
          refine ⟨24078485228980608319942865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64209293943948288853180973 24078485228980608319942865)
          ·
            refine ⟨18058863921735456239957149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24078485228980608319942865 18058863921735456239957149)
            ·
              refine ⟨6772073970650796089983931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18058863921735456239957149 6772073970650796089983931)
              ·
                refine ⟨10158110955976194134975897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6772073970650796089983931 10158110955976194134975897)
                ·
                  refine ⟨7618583216982145601231923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10158110955976194134975897 7618583216982145601231923)
                  ·
                    refine ⟨11427874825473218401847885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7618583216982145601231923 11427874825473218401847885)
                    ·
                      refine ⟨4285453059552456900692957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11427874825473218401847885 4285453059552456900692957)
                      ·
                        rfl

theorem cell23_8345890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_8345890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345890 prefixEnd_8345890 := by exact prefixLift 8345890
  have htrace : WordTrace (prefixWord ++ tailWord_8345890) baseStart_8345890 baseEnd_8345890 := by
    simpa [prefixWord, tailWord_8345890, baseEnd_8345890] using wordTrace_append hprefix tailTrace_8345890
  have hstable : (prefixWord ++ tailWord_8345890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345890).length < 2 ^ (prefixWord ++ tailWord_8345890).sum := by decide
  have hdescent : baseEnd_8345890 < baseStart_8345890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345913 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 4, 2, 2]
def baseStart_8345913 : Nat := 118140960795 + 8345913 * 2 ^ 59
def prefixEnd_8345913 : Nat := 4983230072969 + 3 ^ 40 * 8345913 * 2
def baseEnd_8345913 : Nat := 4285464869607510310705351

theorem tailTrace_8345913 : CollatzResearch.WordTrace tailWord_8345913 prefixEnd_8345913 4285464869607510310705351 := by
  unfold tailWord_8345913
  simp only [CollatzResearch.WordTrace]
  refine ⟨304400454613190044306130393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202933636408793362870753595 304400454613190044306130393)
  ·
    refine ⟨228300340959892533229597795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304400454613190044306130393 228300340959892533229597795)
    ·
      refine ⟨342450511439838799844396693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228300340959892533229597795 342450511439838799844396693)
      ·
        refine ⟨16052367723742443742706095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 342450511439838799844396693 16052367723742443742706095)
        ·
          refine ⟨24078551585613665614059143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16052367723742443742706095 24078551585613665614059143)
          ·
            refine ⟨36117827378420498421088715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24078551585613665614059143 36117827378420498421088715)
            ·
              refine ⟨54176741067630747631633073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36117827378420498421088715 54176741067630747631633073)
              ·
                refine ⟨40632555800723060723724805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54176741067630747631633073 40632555800723060723724805)
                ·
                  refine ⟨7618604212635573885698401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40632555800723060723724805 7618604212635573885698401)
                  ·
                    refine ⟨5713953159476680414273801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7618604212635573885698401 5713953159476680414273801)
                    ·
                      refine ⟨4285464869607510310705351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5713953159476680414273801 4285464869607510310705351)
                      ·
                        rfl

theorem cell23_8345913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_8345913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345913 prefixEnd_8345913 := by exact prefixLift 8345913
  have htrace : WordTrace (prefixWord ++ tailWord_8345913) baseStart_8345913 baseEnd_8345913 := by
    simpa [prefixWord, tailWord_8345913, baseEnd_8345913] using wordTrace_append hprefix tailTrace_8345913
  have hstable : (prefixWord ++ tailWord_8345913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345913).length < 2 ^ (prefixWord ++ tailWord_8345913).sum := by decide
  have hdescent : baseEnd_8345913 < baseStart_8345913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8345989 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 3, 4, 3]
def baseStart_8345989 : Nat := 118140960795 + 8345989 * 2 ^ 59
def prefixEnd_8345989 : Nat := 4983230072969 + 3 ^ 40 * 8345989 * 2
def baseEnd_8345989 : Nat := 4285503894137252013355001

theorem tailTrace_8345989 : CollatzResearch.WordTrace tailWord_8345989 prefixEnd_8345989 4285503894137252013355001 := by
  unfold tailWord_8345989
  simp only [CollatzResearch.WordTrace]
  refine ⟨304403226560914709285897021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202935484373943139523931347 304403226560914709285897021)
  ·
    refine ⟨114151209960343015982211383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304403226560914709285897021 114151209960343015982211383)
    ·
      refine ⟨171226814940514523973317075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114151209960343015982211383 171226814940514523973317075)
      ·
        refine ⟨256840222410771785959975613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171226814940514523973317075 256840222410771785959975613)
        ·
          refine ⟨96315083404039419734990855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256840222410771785959975613 96315083404039419734990855)
          ·
            refine ⟨144472625106059129602486283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96315083404039419734990855 144472625106059129602486283)
            ·
              refine ⟨216708937659088694403729425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144472625106059129602486283 216708937659088694403729425)
              ·
                refine ⟨162531703244316520802797069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216708937659088694403729425 162531703244316520802797069)
                ·
                  refine ⟨60949388716618695301048901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162531703244316520802797069 60949388716618695301048901)
                  ·
                    refine ⟨11428010384366005368946669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60949388716618695301048901 11428010384366005368946669)
                    ·
                      refine ⟨4285503894137252013355001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11428010384366005368946669 4285503894137252013355001)
                      ·
                        rfl

theorem cell23_8345989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_8345989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8345989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8345989 prefixEnd_8345989 := by exact prefixLift 8345989
  have htrace : WordTrace (prefixWord ++ tailWord_8345989) baseStart_8345989 baseEnd_8345989 := by
    simpa [prefixWord, tailWord_8345989, baseEnd_8345989] using wordTrace_append hprefix tailTrace_8345989
  have hstable : (prefixWord ++ tailWord_8345989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8345989).length < 2 ^ (prefixWord ++ tailWord_8345989).sum := by decide
  have hdescent : baseEnd_8345989 < baseStart_8345989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8345989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346009 : List Nat := [1, 2, 1, 2, 1, 4, 1, 5, 6]
def baseStart_8346009 : Nat := 118140960795 + 8346009 * 2 ^ 59
def prefixEnd_8346009 : Nat := 4983230072969 + 3 ^ 40 * 8346009 * 2
def baseEnd_8346009 : Nat := 476168240416704659456101

theorem tailTrace_8346009 : CollatzResearch.WordTrace tailWord_8346009 prefixEnd_8346009 476168240416704659456101 := by
  unfold tailWord_8346009
  simp only [CollatzResearch.WordTrace]
  refine ⟨304403956020842252701625081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202935970680561501801083387 304403956020842252701625081)
  ·
    refine ⟨228302967015631689526218811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304403956020842252701625081 228302967015631689526218811)
    ·
      refine ⟨342454450523447534289328217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228302967015631689526218811 342454450523447534289328217)
      ·
        refine ⟨256840837892585650716996163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342454450523447534289328217 256840837892585650716996163)
        ·
          refine ⟨385261256838878476075494245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256840837892585650716996163 385261256838878476075494245)
          ·
            refine ⟨72236485657289714264155171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 385261256838878476075494245 72236485657289714264155171)
            ·
              refine ⟨108354728485934571396232757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72236485657289714264155171 108354728485934571396232757)
              ·
                refine ⟨10158255795556366068396821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108354728485934571396232757 10158255795556366068396821)
                ·
                  refine ⟨476168240416704659456101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10158255795556366068396821 476168240416704659456101)
                  ·
                    rfl

theorem cell23_8346009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 6].length) (baseStart_8346009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346009 prefixEnd_8346009 := by exact prefixLift 8346009
  have htrace : WordTrace (prefixWord ++ tailWord_8346009) baseStart_8346009 baseEnd_8346009 := by
    simpa [prefixWord, tailWord_8346009, baseEnd_8346009] using wordTrace_append hprefix tailTrace_8346009
  have hstable : (prefixWord ++ tailWord_8346009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346009).length < 2 ^ (prefixWord ++ tailWord_8346009).sum := by decide
  have hdescent : baseEnd_8346009 < baseStart_8346009 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346013 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_8346013 : Nat := 118140960795 + 8346013 * 2 ^ 59
def prefixEnd_8346013 : Nat := 4983230072969 + 3 ^ 40 * 8346013 * 2
def baseEnd_8346013 : Nat := 1428505405890986639818297

theorem tailTrace_8346013 : CollatzResearch.WordTrace tailWord_8346013 prefixEnd_8346013 1428505405890986639818297 := by
  unfold tailWord_8346013
  simp only [CollatzResearch.WordTrace]
  refine ⟨304404101912827761384770693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202936067941885174256513795 304404101912827761384770693)
  ·
    refine ⟨57075769108655205259644505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304404101912827761384770693 57075769108655205259644505)
    ·
      refine ⟨42806826831491403944733379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57075769108655205259644505 42806826831491403944733379)
      ·
        refine ⟨64210240247237105917100069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42806826831491403944733379 64210240247237105917100069)
        ·
          refine ⟨12039420046356957359456263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64210240247237105917100069 12039420046356957359456263)
          ·
            refine ⟨18059130069535436039184395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12039420046356957359456263 18059130069535436039184395)
            ·
              refine ⟨27088695104303154058776593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18059130069535436039184395 27088695104303154058776593)
              ·
                refine ⟨20316521328227365544082445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27088695104303154058776593 20316521328227365544082445)
                ·
                  refine ⟨7618695498085262079030917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20316521328227365544082445 7618695498085262079030917)
                  ·
                    refine ⟨1428505405890986639818297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7618695498085262079030917 1428505405890986639818297)
                    ·
                      rfl

theorem cell23_8346013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_8346013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346013 prefixEnd_8346013 := by exact prefixLift 8346013
  have htrace : WordTrace (prefixWord ++ tailWord_8346013) baseStart_8346013 baseEnd_8346013 := by
    simpa [prefixWord, tailWord_8346013, baseEnd_8346013] using wordTrace_append hprefix tailTrace_8346013
  have hstable : (prefixWord ++ tailWord_8346013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346013).length < 2 ^ (prefixWord ++ tailWord_8346013).sum := by decide
  have hdescent : baseEnd_8346013 < baseStart_8346013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346023 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_8346023 : Nat := 118140960795 + 8346023 * 2 ^ 59
def prefixEnd_8346023 : Nat := 4983230072969 + 3 ^ 40 * 8346023 * 2
def baseEnd_8346023 : Nat := 4285521352479504880329845

theorem tailTrace_8346023 : CollatzResearch.WordTrace tailWord_8346023 prefixEnd_8346023 4285521352479504880329845 := by
  unfold tailWord_8346023
  simp only [CollatzResearch.WordTrace]
  refine ⟨304404466642791533092634723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202936311095194355395089815 304404466642791533092634723)
  ·
    refine ⟨456606699964187299638952085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304404466642791533092634723 456606699964187299638952085)
    ·
      refine ⟨21403439060821279670575879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 456606699964187299638952085 21403439060821279670575879)
      ·
        refine ⟨32105158591231919505863819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21403439060821279670575879 32105158591231919505863819)
        ·
          refine ⟨48157737886847879258795729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32105158591231919505863819 48157737886847879258795729)
          ·
            refine ⟨36118303415135909444096797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48157737886847879258795729 36118303415135909444096797)
            ·
              refine ⟨13544363780675966041536299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36118303415135909444096797 13544363780675966041536299)
              ·
                refine ⟨20316545671013949062304449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13544363780675966041536299 20316545671013949062304449)
                ·
                  refine ⟨15237409253260461796728337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20316545671013949062304449 15237409253260461796728337)
                  ·
                    refine ⟨11428056939945346347546253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15237409253260461796728337 11428056939945346347546253)
                    ·
                      refine ⟨4285521352479504880329845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11428056939945346347546253 4285521352479504880329845)
                      ·
                        rfl

theorem cell23_8346023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_8346023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346023 prefixEnd_8346023 := by exact prefixLift 8346023
  have htrace : WordTrace (prefixWord ++ tailWord_8346023) baseStart_8346023 baseEnd_8346023 := by
    simpa [prefixWord, tailWord_8346023, baseEnd_8346023] using wordTrace_append hprefix tailTrace_8346023
  have hstable : (prefixWord ++ tailWord_8346023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346023).length < 2 ^ (prefixWord ++ tailWord_8346023).sum := by decide
  have hdescent : baseEnd_8346023 < baseStart_8346023 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346070 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_8346070 : Nat := 118140960795 + 8346070 * 2 ^ 59
def prefixEnd_8346070 : Nat := 4983230072969 + 3 ^ 40 * 8346070 * 2
def baseEnd_8346070 : Nat := 4285545486070266196442129

theorem tailTrace_8346070 : CollatzResearch.WordTrace tailWord_8346070 prefixEnd_8346070 4285545486070266196442129 := by
  unfold tailWord_8346070
  simp only [CollatzResearch.WordTrace]
  refine ⟨19025386304601328757474729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202937453915747506746397109 19025386304601328757474729)
  ·
    refine ⟨14269039728450996568106047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19025386304601328757474729 14269039728450996568106047)
    ·
      refine ⟨21403559592676494852159071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14269039728450996568106047 21403559592676494852159071)
      ·
        refine ⟨32105339389014742278238607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21403559592676494852159071 32105339389014742278238607)
        ·
          refine ⟨48158009083522113417357911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32105339389014742278238607 48158009083522113417357911)
          ·
            refine ⟨72237013625283170126036867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48158009083522113417357911 72237013625283170126036867)
            ·
              refine ⟨108355520437924755189055301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72237013625283170126036867 108355520437924755189055301)
              ·
                refine ⟨20316660082110891597947869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108355520437924755189055301 20316660082110891597947869)
                ·
                  refine ⟨7618747530791584349230451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20316660082110891597947869 7618747530791584349230451)
                  ·
                    refine ⟨11428121296187376523845677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7618747530791584349230451 11428121296187376523845677)
                    ·
                      refine ⟨4285545486070266196442129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11428121296187376523845677 4285545486070266196442129)
                      ·
                        rfl

theorem cell23_8346070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_8346070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346070 prefixEnd_8346070 := by exact prefixLift 8346070
  have htrace : WordTrace (prefixWord ++ tailWord_8346070) baseStart_8346070 baseEnd_8346070 := by
    simpa [prefixWord, tailWord_8346070, baseEnd_8346070] using wordTrace_append hprefix tailTrace_8346070
  have hstable : (prefixWord ++ tailWord_8346070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346070).length < 2 ^ (prefixWord ++ tailWord_8346070).sum := by decide
  have hdescent : baseEnd_8346070 < baseStart_8346070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346096 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 5]
def baseStart_8346096 : Nat := 118140960795 + 8346096 * 2 ^ 59
def prefixEnd_8346096 : Nat := 4983230072969 + 3 ^ 40 * 8346096 * 2
def baseEnd_8346096 : Nat := 4285558836567283094717009

theorem tailTrace_8346096 : CollatzResearch.WordTrace tailWord_8346096 prefixEnd_8346096 4285558836567283094717009 := by
  unfold tailWord_8346096
  simp only [CollatzResearch.WordTrace]
  refine ⟨152203564585763533280021071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202938086114351377706694761 152203564585763533280021071)
  ·
    refine ⟨228305346878645299920031607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152203564585763533280021071 228305346878645299920031607)
    ·
      refine ⟨342458020317967949880047411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228305346878645299920031607 342458020317967949880047411)
      ·
        refine ⟨513687030476951924820071117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342458020317967949880047411 513687030476951924820071117)
        ·
          refine ⟨192632636428856971807526669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513687030476951924820071117 192632636428856971807526669)
          ·
            refine ⟨72237238660821364427822501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192632636428856971807526669 72237238660821364427822501)
            ·
              refine ⟨13544482248904005830216719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72237238660821364427822501 13544482248904005830216719)
              ·
                refine ⟨20316723373356008745325079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13544482248904005830216719 20316723373356008745325079)
                ·
                  refine ⟨30475085060034013117987619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20316723373356008745325079 30475085060034013117987619)
                  ·
                    refine ⟨45712627590051019676981429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30475085060034013117987619 45712627590051019676981429)
                    ·
                      refine ⟨4285558836567283094717009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45712627590051019676981429 4285558836567283094717009)
                      ·
                        rfl

theorem cell23_8346096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 5].length) (baseStart_8346096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346096 prefixEnd_8346096 := by exact prefixLift 8346096
  have htrace : WordTrace (prefixWord ++ tailWord_8346096) baseStart_8346096 baseEnd_8346096 := by
    simpa [prefixWord, tailWord_8346096, baseEnd_8346096] using wordTrace_append hprefix tailTrace_8346096
  have hstable : (prefixWord ++ tailWord_8346096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346096).length < 2 ^ (prefixWord ++ tailWord_8346096).sum := by decide
  have hdescent : baseEnd_8346096 < baseStart_8346096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346116 : List Nat := [2, 3, 2, 3, 1, 1, 1, 10]
def baseStart_8346116 : Nat := 118140960795 + 8346116 * 2 ^ 59
def prefixEnd_8346116 : Nat := 4983230072969 + 3 ^ 40 * 8346116 * 2
def baseEnd_8346116 : Nat := 158724781710384185795071

theorem tailTrace_8346116 : CollatzResearch.WordTrace tailWord_8346116 prefixEnd_8346116 158724781710384185795071 := by
  unfold tailWord_8346116
  simp only [CollatzResearch.WordTrace]
  refine ⟨152203929315727304987885101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202938572420969739983846801 152203929315727304987885101)
  ·
    refine ⟨57076473493397739370456913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152203929315727304987885101 57076473493397739370456913)
    ·
      refine ⟨42807355120048304527842685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57076473493397739370456913 42807355120048304527842685)
      ·
        refine ⟨16052758170018114197941007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42807355120048304527842685 16052758170018114197941007)
        ·
          refine ⟨24079137255027171296911511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16052758170018114197941007 24079137255027171296911511)
          ·
            refine ⟨36118705882540756945367267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24079137255027171296911511 36118705882540756945367267)
            ·
              refine ⟨54178058823811135418050901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36118705882540756945367267 54178058823811135418050901)
              ·
                refine ⟨158724781710384185795071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 54178058823811135418050901 158724781710384185795071)
                ·
                  rfl

theorem cell23_8346116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 10].length) (baseStart_8346116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346116 prefixEnd_8346116 := by exact prefixLift 8346116
  have htrace : WordTrace (prefixWord ++ tailWord_8346116) baseStart_8346116 baseEnd_8346116 := by
    simpa [prefixWord, tailWord_8346116, baseEnd_8346116] using wordTrace_append hprefix tailTrace_8346116
  have hstable : (prefixWord ++ tailWord_8346116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346116).length < 2 ^ (prefixWord ++ tailWord_8346116).sum := by decide
  have hdescent : baseEnd_8346116 < baseStart_8346116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346129 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 4, 7]
def baseStart_8346129 : Nat := 118140960795 + 8346129 * 2 ^ 59
def prefixEnd_8346129 : Nat := 4983230072969 + 3 ^ 40 * 8346129 * 2
def baseEnd_8346129 : Nat := 1428525260476293821868119

theorem tailTrace_8346129 : CollatzResearch.WordTrace tailWord_8346129 prefixEnd_8346129 1428525260476293821868119 := by
  unfold tailWord_8346129
  simp only [CollatzResearch.WordTrace]
  refine ⟨304408332780407513195993441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202938888520271675463995627 304408332780407513195993441)
  ·
    refine ⟨228306249585305634896995081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304408332780407513195993441 228306249585305634896995081)
    ·
      refine ⟨171229687188979226172746311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228306249585305634896995081 171229687188979226172746311)
      ·
        refine ⟨256844530783468839259119467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171229687188979226172746311 256844530783468839259119467)
        ·
          refine ⟨385266796175203258888679201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256844530783468839259119467 385266796175203258888679201)
          ·
            refine ⟨288950097131402444166509401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385266796175203258888679201 288950097131402444166509401)
            ·
              refine ⟨216712572848551833124882051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288950097131402444166509401 216712572848551833124882051)
              ·
                refine ⟨325068859272827749687323077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216712572848551833124882051 325068859272827749687323077)
                ·
                  refine ⟨60950411113655203066373077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325068859272827749687323077 60950411113655203066373077)
                  ·
                    refine ⟨1428525260476293821868119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60950411113655203066373077 1428525260476293821868119)
                    ·
                      rfl

theorem cell23_8346129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_8346129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346129 prefixEnd_8346129 := by exact prefixLift 8346129
  have htrace : WordTrace (prefixWord ++ tailWord_8346129) baseStart_8346129 baseEnd_8346129 := by
    simpa [prefixWord, tailWord_8346129, baseEnd_8346129] using wordTrace_append hprefix tailTrace_8346129
  have hstable : (prefixWord ++ tailWord_8346129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346129).length < 2 ^ (prefixWord ++ tailWord_8346129).sum := by decide
  have hdescent : baseEnd_8346129 < baseStart_8346129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346159 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 5, 8]
def baseStart_8346159 : Nat := 118140960795 + 8346159 * 2 ^ 59
def prefixEnd_8346159 : Nat := 4983230072969 + 3 ^ 40 * 8346159 * 2
def baseEnd_8346159 : Nat := 1428530395282838782743073

theorem tailTrace_8346159 : CollatzResearch.WordTrace tailWord_8346159 prefixEnd_8346159 1428530395282838782743073 := by
  unfold tailWord_8346159
  simp only [CollatzResearch.WordTrace]
  refine ⟨304409426970298828319585531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202939617980199218879723687 304409426970298828319585531)
  ·
    refine ⟨456614140455448242479378297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304409426970298828319585531 456614140455448242479378297)
    ·
      refine ⟨342460605341586181859533723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456614140455448242479378297 342460605341586181859533723)
      ·
        refine ⟨513690908012379272789300585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342460605341586181859533723 513690908012379272789300585)
        ·
          refine ⟨385268181009284454591975439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513690908012379272789300585 385268181009284454591975439)
          ·
            refine ⟨577902271513926681887963159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385268181009284454591975439 577902271513926681887963159)
            ·
              refine ⟨866853407270890022831944739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577902271513926681887963159 866853407270890022831944739)
              ·
                refine ⟨1300280110906335034247917109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866853407270890022831944739 1300280110906335034247917109)
                ·
                  refine ⟨121901260397468909460742229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1300280110906335034247917109 121901260397468909460742229)
                  ·
                    refine ⟨1428530395282838782743073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121901260397468909460742229 1428530395282838782743073)
                    ·
                      rfl

theorem cell23_8346159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_8346159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346159 prefixEnd_8346159 := by exact prefixLift 8346159
  have htrace : WordTrace (prefixWord ++ tailWord_8346159) baseStart_8346159 baseEnd_8346159 := by
    simpa [prefixWord, tailWord_8346159, baseEnd_8346159] using wordTrace_append hprefix tailTrace_8346159
  have hstable : (prefixWord ++ tailWord_8346159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346159).length < 2 ^ (prefixWord ++ tailWord_8346159).sum := by decide
  have hdescent : baseEnd_8346159 < baseStart_8346159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346223 : List Nat := [1, 1, 2, 1, 3, 2, 4, 4, 5]
def baseStart_8346223 : Nat := 118140960795 + 8346223 * 2 ^ 59
def prefixEnd_8346223 : Nat := 4983230072969 + 3 ^ 40 * 8346223 * 2
def baseEnd_8346223 : Nat := 476180449845600455314325

theorem tailTrace_8346223 : CollatzResearch.WordTrace tailWord_8346223 prefixEnd_8346223 476180449845600455314325 := by
  unfold tailWord_8346223
  simp only [CollatzResearch.WordTrace]
  refine ⟨304411761242066967249915323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202941174161377978166610215 304411761242066967249915323)
  ·
    refine ⟨456617641863100450874872985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304411761242066967249915323 456617641863100450874872985)
    ·
      refine ⟨342463231397325338156154739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456617641863100450874872985 342463231397325338156154739)
      ·
        refine ⟨513694847095988007234232109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342463231397325338156154739 513694847095988007234232109)
        ·
          refine ⟨192635567660995502712837041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513694847095988007234232109 192635567660995502712837041)
          ·
            refine ⟨144476675745746627034627781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192635567660995502712837041 144476675745746627034627781)
            ·
              refine ⟨27089376702327492568992709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144476675745746627034627781 27089376702327492568992709)
              ·
                refine ⟨5079258131686404856686133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27089376702327492568992709 5079258131686404856686133)
                ·
                  refine ⟨476180449845600455314325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5079258131686404856686133 476180449845600455314325)
                  ·
                    rfl

theorem cell23_8346223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 5].length) (baseStart_8346223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346223 prefixEnd_8346223 := by exact prefixLift 8346223
  have htrace : WordTrace (prefixWord ++ tailWord_8346223) baseStart_8346223 baseEnd_8346223 := by
    simpa [prefixWord, tailWord_8346223, baseEnd_8346223] using wordTrace_append hprefix tailTrace_8346223
  have hstable : (prefixWord ++ tailWord_8346223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346223).length < 2 ^ (prefixWord ++ tailWord_8346223).sum := by decide
  have hdescent : baseEnd_8346223 < baseStart_8346223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346233 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 2, 3, 3]
def baseStart_8346233 : Nat := 118140960795 + 8346233 * 2 ^ 59
def prefixEnd_8346233 : Nat := 4983230072969 + 3 ^ 40 * 8346233 * 2
def baseEnd_8346233 : Nat := 4285629183416949058703879

theorem tailTrace_8346233 : CollatzResearch.WordTrace tailWord_8346233 prefixEnd_8346233 4285629183416949058703879 := by
  unfold tailWord_8346233
  simp only [CollatzResearch.WordTrace]
  refine ⟨304412125972030738957779353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202941417314687159305186235 304412125972030738957779353)
  ·
    refine ⟨228309094479023054218334515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304412125972030738957779353 228309094479023054218334515)
    ·
      refine ⟨342463641718534581327501773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228309094479023054218334515 342463641718534581327501773)
      ·
        refine ⟨128423865644450467997813165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342463641718534581327501773 128423865644450467997813165)
        ·
          refine ⟨48158949616668925499179937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128423865644450467997813165 48158949616668925499179937)
          ·
            refine ⟨36119212212501694124384953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48158949616668925499179937 36119212212501694124384953)
            ·
              refine ⟨27089409159376270593288715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36119212212501694124384953 27089409159376270593288715)
              ·
                refine ⟨40634113739064405889933073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27089409159376270593288715 40634113739064405889933073)
                ·
                  refine ⟨30475585304298304417449805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40634113739064405889933073 30475585304298304417449805)
                  ·
                    refine ⟨11428344489111864156543677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30475585304298304417449805 11428344489111864156543677)
                    ·
                      refine ⟨4285629183416949058703879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11428344489111864156543677 4285629183416949058703879)
                      ·
                        rfl

theorem cell23_8346233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_8346233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346233 prefixEnd_8346233 := by exact prefixLift 8346233
  have htrace : WordTrace (prefixWord ++ tailWord_8346233) baseStart_8346233 baseEnd_8346233 := by
    simpa [prefixWord, tailWord_8346233, baseEnd_8346233] using wordTrace_append hprefix tailTrace_8346233
  have hstable : (prefixWord ++ tailWord_8346233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346233).length < 2 ^ (prefixWord ++ tailWord_8346233).sum := by decide
  have hdescent : baseEnd_8346233 < baseStart_8346233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346236 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 1, 7]
def baseStart_8346236 : Nat := 118140960795 + 8346236 * 2 ^ 59
def prefixEnd_8346236 : Nat := 4983230072969 + 3 ^ 40 * 8346236 * 2
def baseEnd_8346236 : Nat := 1428543574619637515655455

theorem tailTrace_8346236 : CollatzResearch.WordTrace tailWord_8346236 prefixEnd_8346236 1428543574619637515655455 := by
  unfold tailWord_8346236
  simp only [CollatzResearch.WordTrace]
  refine ⟨152206117695509935235069281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202941490260679913646759041 152206117695509935235069281)
  ·
    refine ⟨114154588271632451426301961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152206117695509935235069281 114154588271632451426301961)
    ·
      refine ⟨85615941203724338569726471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114154588271632451426301961 85615941203724338569726471)
      ·
        refine ⟨128423911805586507854589707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85615941203724338569726471 128423911805586507854589707)
        ·
          refine ⟨192635867708379761781884561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128423911805586507854589707 192635867708379761781884561)
          ·
            refine ⟨144476900781284821336413421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192635867708379761781884561 144476900781284821336413421)
            ·
              refine ⟨54178837792981808001155033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144476900781284821336413421 54178837792981808001155033)
              ·
                refine ⟨40634128344736356000866275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54178837792981808001155033 40634128344736356000866275)
                ·
                  refine ⟨60951192517104534001299413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40634128344736356000866275 60951192517104534001299413)
                  ·
                    refine ⟨1428543574619637515655455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60951192517104534001299413 1428543574619637515655455)
                    ·
                      rfl

theorem cell23_8346236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_8346236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346236 prefixEnd_8346236 := by exact prefixLift 8346236
  have htrace : WordTrace (prefixWord ++ tailWord_8346236) baseStart_8346236 baseEnd_8346236 := by
    simpa [prefixWord, tailWord_8346236, baseEnd_8346236] using wordTrace_append hprefix tailTrace_8346236
  have hstable : (prefixWord ++ tailWord_8346236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346236).length < 2 ^ (prefixWord ++ tailWord_8346236).sum := by decide
  have hdescent : baseEnd_8346236 < baseStart_8346236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
