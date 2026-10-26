import V185TrunkScan22Chunk026

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_240976 : List Nat := [2, 1, 1, 1, 1, 5, 1, 5, 2, 3]
def baseStart_240976 : Nat := 118140960795 + 240976 * 2 ^ 59
def prefixEnd_240976 : Nat := 4983230072969 + 3 ^ 40 * 240976 * 2
def baseEnd_240976 : Nat := 82491009465302942661185

theorem tailTrace_240976 : CollatzResearch.WordTrace tailWord_240976 prefixEnd_240976 82491009465302942661185 := by
  unfold tailWord_240976
  simp only [CollatzResearch.WordTrace]
  refine ⟨4394558387496291134679391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5859411183328388179572521 4394558387496291134679391)
  ·
    refine ⟨6591837581244436702019087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4394558387496291134679391 6591837581244436702019087)
    ·
      refine ⟨9887756371866655053028631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6591837581244436702019087 9887756371866655053028631)
      ·
        refine ⟨14831634557799982579542947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9887756371866655053028631 14831634557799982579542947)
        ·
          refine ⟨22247451836699973869314421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14831634557799982579542947 22247451836699973869314421)
          ·
            refine ⟨2085698609690622550248227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22247451836699973869314421 2085698609690622550248227)
            ·
              refine ⟨3128547914535933825372341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085698609690622550248227 3128547914535933825372341)
              ·
                refine ⟨293301366987743796128657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3128547914535933825372341 293301366987743796128657)
                ·
                  refine ⟨219976025240807847096493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293301366987743796128657 219976025240807847096493)
                  ·
                    refine ⟨82491009465302942661185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 219976025240807847096493 82491009465302942661185)
                    ·
                      rfl

theorem cell22_240976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 2, 3].length) (baseStart_240976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240976 prefixEnd_240976 := by exact prefixLift 240976
  have htrace : WordTrace (prefixWord ++ tailWord_240976) baseStart_240976 baseEnd_240976 := by
    simpa [prefixWord, tailWord_240976, baseEnd_240976] using wordTrace_append hprefix tailTrace_240976
  have hstable : (prefixWord ++ tailWord_240976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240976).length < 2 ^ (prefixWord ++ tailWord_240976).sum := by decide
  have hdescent : baseEnd_240976 < baseStart_240976 := by decide
  rcases family_descends (prefixWord ++ tailWord_240976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241055 : List Nat := [1, 1, 2, 5, 1, 2, 3, 3, 1, 3]
def baseStart_241055 : Nat := 118140960795 + 241055 * 2 ^ 59
def prefixEnd_241055 : Nat := 4983230072969 + 3 ^ 40 * 241055 * 2
def baseEnd_241055 : Nat := 82518052779773069935943

theorem tailTrace_241055 : CollatzResearch.WordTrace tailWord_241055 prefixEnd_241055 82518052779773069935943 := by
  unfold tailWord_241055
  simp only [CollatzResearch.WordTrace]
  refine ⟨8791998141706378761484619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5861332094470919174323079 8791998141706378761484619)
  ·
    refine ⟨13187997212559568142226929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8791998141706378761484619 13187997212559568142226929)
    ·
      refine ⟨9890997909419676106670197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13187997212559568142226929 9890997909419676106670197)
      ·
        refine ⟨927281054008094635000331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9890997909419676106670197 927281054008094635000331)
        ·
          refine ⟨1390921581012141952500497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927281054008094635000331 1390921581012141952500497)
          ·
            refine ⟨1043191185759106464375373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1390921581012141952500497 1043191185759106464375373)
            ·
              refine ⟨391196694659664924140765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1043191185759106464375373 391196694659664924140765)
              ·
                refine ⟨146698760497374346552787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391196694659664924140765 146698760497374346552787)
                ·
                  refine ⟨220048140746061519829181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146698760497374346552787 220048140746061519829181)
                  ·
                    refine ⟨82518052779773069935943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 220048140746061519829181 82518052779773069935943)
                    ·
                      rfl

theorem cell22_241055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 1, 3].length) (baseStart_241055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241055 prefixEnd_241055 := by exact prefixLift 241055
  have htrace : WordTrace (prefixWord ++ tailWord_241055) baseStart_241055 baseEnd_241055 := by
    simpa [prefixWord, tailWord_241055, baseEnd_241055] using wordTrace_append hprefix tailTrace_241055
  have hstable : (prefixWord ++ tailWord_241055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241055).length < 2 ^ (prefixWord ++ tailWord_241055).sum := by decide
  have hdescent : baseEnd_241055 < baseStart_241055 := by decide
  rcases family_descends (prefixWord ++ tailWord_241055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241098 : List Nat := [3, 1, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_241098 : Nat := 118140960795 + 241098 * 2 ^ 59
def prefixEnd_241098 : Nat := 4983230072969 + 3 ^ 40 * 241098 * 2
def baseEnd_241098 : Nat := 82532772558535291110811

theorem tailTrace_241098 : CollatzResearch.WordTrace tailWord_241098 prefixEnd_241098 82532772558535291110811 := by
  unfold tailWord_241098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2198391620137649276324987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5862377653700398070199965 2198391620137649276324987)
  ·
    refine ⟨3297587430206473914487481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2198391620137649276324987 3297587430206473914487481)
    ·
      refine ⟨2473190572654855435865611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3297587430206473914487481 2473190572654855435865611)
      ·
        refine ⟨3709785858982283153798417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2473190572654855435865611 3709785858982283153798417)
        ·
          refine ⟨2782339394236712365348813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3709785858982283153798417 2782339394236712365348813)
          ·
            refine ⟨1043377272838767137005805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2782339394236712365348813 1043377272838767137005805)
            ·
              refine ⟨391266477314537676377177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1043377272838767137005805 391266477314537676377177)
              ·
                refine ⟨293449857985903257282883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391266477314537676377177 293449857985903257282883)
                ·
                  refine ⟨440174786978854885924325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293449857985903257282883 440174786978854885924325)
                  ·
                    refine ⟨82532772558535291110811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 440174786978854885924325 82532772558535291110811)
                    ·
                      rfl

theorem cell22_241098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_241098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241098 prefixEnd_241098 := by exact prefixLift 241098
  have htrace : WordTrace (prefixWord ++ tailWord_241098) baseStart_241098 baseEnd_241098 := by
    simpa [prefixWord, tailWord_241098, baseEnd_241098] using wordTrace_append hprefix tailTrace_241098
  have hstable : (prefixWord ++ tailWord_241098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241098).length < 2 ^ (prefixWord ++ tailWord_241098).sum := by decide
  have hdescent : baseEnd_241098 < baseStart_241098 := by decide
  rcases family_descends (prefixWord ++ tailWord_241098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241111 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 6, 3]
def baseStart_241111 : Nat := 118140960795 + 241111 * 2 ^ 59
def prefixEnd_241111 : Nat := 4983230072969 + 3 ^ 40 * 241111 * 2
def baseEnd_241111 : Nat := 82537222724207590535771

theorem tailTrace_241111 : CollatzResearch.WordTrace tailWord_241111 prefixEnd_241111 82537222724207590535771 := by
  unfold tailWord_241111
  simp only [CollatzResearch.WordTrace]
  refine ⟨8794040629503500325523187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5862693753002333550348791 8794040629503500325523187)
  ·
    refine ⟨13191060944255250488284781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8794040629503500325523187 13191060944255250488284781)
    ·
      refine ⟨4946647854095718933106793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13191060944255250488284781 4946647854095718933106793)
      ·
        refine ⟨3709985890571789199830095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4946647854095718933106793 3709985890571789199830095)
        ·
          refine ⟨5564978835857683799745143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3709985890571789199830095 5564978835857683799745143)
          ·
            refine ⟨8347468253786525699617715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564978835857683799745143 8347468253786525699617715)
            ·
              refine ⟨12521202380679788549426573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8347468253786525699617715 12521202380679788549426573)
              ·
                refine ⟨4695450892754920706034965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12521202380679788549426573 4695450892754920706034965)
                ·
                  refine ⟨220099260597886908095389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4695450892754920706034965 220099260597886908095389)
                  ·
                    refine ⟨82537222724207590535771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 220099260597886908095389 82537222724207590535771)
                    ·
                      rfl

theorem cell22_241111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_241111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241111 prefixEnd_241111 := by exact prefixLift 241111
  have htrace : WordTrace (prefixWord ++ tailWord_241111) baseStart_241111 baseEnd_241111 := by
    simpa [prefixWord, tailWord_241111, baseEnd_241111] using wordTrace_append hprefix tailTrace_241111
  have hstable : (prefixWord ++ tailWord_241111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241111).length < 2 ^ (prefixWord ++ tailWord_241111).sum := by decide
  have hdescent : baseEnd_241111 < baseStart_241111 := by decide
  rcases family_descends (prefixWord ++ tailWord_241111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241130 : List Nat := [3, 1, 3, 1, 4, 1, 1, 4, 4]
def baseStart_241130 : Nat := 118140960795 + 241130 * 2 ^ 59
def prefixEnd_241130 : Nat := 4983230072969 + 3 ^ 40 * 241130 * 2
def baseEnd_241130 : Nat := 27514575604165958103571

theorem tailTrace_241130 : CollatzResearch.WordTrace tailWord_241130 prefixEnd_241130 27514575604165958103571 := by
  unfold tailWord_241130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2198683404108666642616211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5863155744289777713643229 2198683404108666642616211)
  ·
    refine ⟨3298025106162999963924317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2198683404108666642616211 3298025106162999963924317)
    ·
      refine ⟨1236759414811124986471619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3298025106162999963924317 1236759414811124986471619)
      ·
        refine ⟨1855139122216687479707429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1236759414811124986471619 1855139122216687479707429)
        ·
          refine ⟨347838585415628902445143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1855139122216687479707429 347838585415628902445143)
          ·
            refine ⟨521757878123443353667715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347838585415628902445143 521757878123443353667715)
            ·
              refine ⟨782636817185165030501573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521757878123443353667715 782636817185165030501573)
              ·
                refine ⟨146744403222218443219045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 782636817185165030501573 146744403222218443219045)
                ·
                  refine ⟨27514575604165958103571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146744403222218443219045 27514575604165958103571)
                  ·
                    rfl

theorem cell22_241130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_241130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241130 prefixEnd_241130 := by exact prefixLift 241130
  have htrace : WordTrace (prefixWord ++ tailWord_241130) baseStart_241130 baseEnd_241130 := by
    simpa [prefixWord, tailWord_241130, baseEnd_241130] using wordTrace_append hprefix tailTrace_241130
  have hstable : (prefixWord ++ tailWord_241130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241130).length < 2 ^ (prefixWord ++ tailWord_241130).sum := by decide
  have hdescent : baseEnd_241130 < baseStart_241130 := by decide
  rcases family_descends (prefixWord ++ tailWord_241130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241233 : List Nat := [1, 2, 2, 1, 3, 2, 1, 5, 1, 4]
def baseStart_241233 : Nat := 118140960795 + 241233 * 2 ^ 59
def prefixEnd_241233 : Nat := 4983230072969 + 3 ^ 40 * 241233 * 2
def baseEnd_241233 : Nat := 82578985817439938985397

theorem tailTrace_241233 : CollatzResearch.WordTrace tailWord_241233 prefixEnd_241233 82578985817439938985397 := by
  unfold tailWord_241233
  simp only [CollatzResearch.WordTrace]
  refine ⟨8798490335061515161464353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5865660223374343440976235 8798490335061515161464353)
  ·
    refine ⟨6598867751296136371098265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8798490335061515161464353 6598867751296136371098265)
    ·
      refine ⟨4949150813472102278323699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6598867751296136371098265 4949150813472102278323699)
      ·
        refine ⟨7423726220208153417485549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4949150813472102278323699 7423726220208153417485549)
        ·
          refine ⟨2783897332578057531557081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7423726220208153417485549 2783897332578057531557081)
          ·
            refine ⟨2087922999433543148667811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2783897332578057531557081 2087922999433543148667811)
            ·
              refine ⟨3131884499150314723001717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087922999433543148667811 3131884499150314723001717)
              ·
                refine ⟨293614171795342005281411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3131884499150314723001717 293614171795342005281411)
                ·
                  refine ⟨440421257693013007922117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293614171795342005281411 440421257693013007922117)
                  ·
                    refine ⟨82578985817439938985397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 440421257693013007922117 82578985817439938985397)
                    ·
                      rfl

theorem cell22_241233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_241233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241233 prefixEnd_241233 := by exact prefixLift 241233
  have htrace : WordTrace (prefixWord ++ tailWord_241233) baseStart_241233 baseEnd_241233 := by
    simpa [prefixWord, tailWord_241233, baseEnd_241233] using wordTrace_append hprefix tailTrace_241233
  have hstable : (prefixWord ++ tailWord_241233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241233).length < 2 ^ (prefixWord ++ tailWord_241233).sum := by decide
  have hdescent : baseEnd_241233 < baseStart_241233 := by decide
  rcases family_descends (prefixWord ++ tailWord_241233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241310 : List Nat := [4, 3, 1, 1, 1, 2, 3, 7]
def baseStart_241310 : Nat := 118140960795 + 241310 * 2 ^ 59
def prefixEnd_241310 : Nat := 4983230072969 + 3 ^ 40 * 241310 * 2
def baseEnd_241310 : Nat := 9178371610115267201129

theorem tailTrace_241310 : CollatzResearch.WordTrace tailWord_241310 prefixEnd_241310 9178371610115267201129 := by
  unfold tailWord_241310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100162344472819664002173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5867532503855038208011589 1100162344472819664002173)
  ·
    refine ⟨412560879177307374000815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1100162344472819664002173 412560879177307374000815)
    ·
      refine ⟨618841318765961061001223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412560879177307374000815 618841318765961061001223)
      ·
        refine ⟨928261978148941591501835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618841318765961061001223 928261978148941591501835)
        ·
          refine ⟨1392392967223412387252753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928261978148941591501835 1392392967223412387252753)
          ·
            refine ⟨1044294725417559290439565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1392392967223412387252753 1044294725417559290439565)
            ·
              refine ⟨391610522031584733914837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1044294725417559290439565 391610522031584733914837)
              ·
                refine ⟨9178371610115267201129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 391610522031584733914837 9178371610115267201129)
                ·
                  rfl

theorem cell22_241310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_241310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241310 prefixEnd_241310 := by exact prefixLift 241310
  have htrace : WordTrace (prefixWord ++ tailWord_241310) baseStart_241310 baseEnd_241310 := by
    simpa [prefixWord, tailWord_241310, baseEnd_241310] using wordTrace_append hprefix tailTrace_241310
  have hstable : (prefixWord ++ tailWord_241310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241310).length < 2 ^ (prefixWord ++ tailWord_241310).sum := by decide
  have hdescent : baseEnd_241310 < baseStart_241310 := by decide
  rcases family_descends (prefixWord ++ tailWord_241310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241400 : List Nat := [2, 1, 2, 1, 1, 2, 2, 7, 4]
def baseStart_241400 : Nat := 118140960795 + 241400 * 2 ^ 59
def prefixEnd_241400 : Nat := 4983230072969 + 3 ^ 40 * 241400 * 2
def baseEnd_241400 : Nat := 27545384443435723353295

theorem tailTrace_241400 : CollatzResearch.WordTrace tailWord_241400 prefixEnd_241400 27545384443435723353295 := by
  unfold tailWord_241400
  simp only [CollatzResearch.WordTrace]
  refine ⟨4402290662728251341396827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5869720883637668455195769 4402290662728251341396827)
  ·
    refine ⟨6603435994092377012095241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4402290662728251341396827 6603435994092377012095241)
    ·
      refine ⟨4952576995569282759071431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6603435994092377012095241 4952576995569282759071431)
      ·
        refine ⟨7428865493353924138607147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952576995569282759071431 7428865493353924138607147)
        ·
          refine ⟨11143298240030886207910721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7428865493353924138607147 11143298240030886207910721)
          ·
            refine ⟨8357473680023164655933041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11143298240030886207910721 8357473680023164655933041)
            ·
              refine ⟨6268105260017373491949781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8357473680023164655933041 6268105260017373491949781)
              ·
                refine ⟨146908717031657191217573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6268105260017373491949781 146908717031657191217573)
                ·
                  refine ⟨27545384443435723353295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146908717031657191217573 27545384443435723353295)
                  ·
                    rfl

theorem cell22_241400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 4].length) (baseStart_241400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241400 prefixEnd_241400 := by exact prefixLift 241400
  have htrace : WordTrace (prefixWord ++ tailWord_241400) baseStart_241400 baseEnd_241400 := by
    simpa [prefixWord, tailWord_241400, baseEnd_241400] using wordTrace_append hprefix tailTrace_241400
  have hstable : (prefixWord ++ tailWord_241400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241400).length < 2 ^ (prefixWord ++ tailWord_241400).sum := by decide
  have hdescent : baseEnd_241400 < baseStart_241400 := by decide
  rcases family_descends (prefixWord ++ tailWord_241400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241443 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 2, 7]
def baseStart_241443 : Nat := 118140960795 + 241443 * 2 ^ 59
def prefixEnd_241443 : Nat := 4983230072969 + 3 ^ 40 * 241443 * 2
def baseEnd_241443 : Nat := 82650873109069391234753

theorem tailTrace_241443 : CollatzResearch.WordTrace tailWord_241443 prefixEnd_241443 82650873109069391234753 := by
  unfold tailWord_241443
  simp only [CollatzResearch.WordTrace]
  refine ⟨8806149664300721026608983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5870766442867147351072655 8806149664300721026608983)
  ·
    refine ⟨13209224496451081539913475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8806149664300721026608983 13209224496451081539913475)
    ·
      refine ⟨19813836744676622309870213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13209224496451081539913475 19813836744676622309870213)
      ·
        refine ⟨3715094389626866683100665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19813836744676622309870213 3715094389626866683100665)
        ·
          refine ⟨2786320792220150012325499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3715094389626866683100665 2786320792220150012325499)
          ·
            refine ⟨4179481188330225018488249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2786320792220150012325499 4179481188330225018488249)
            ·
              refine ⟨3134610891247668763866187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4179481188330225018488249 3134610891247668763866187)
              ·
                refine ⟨4701916336871503145799281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134610891247668763866187 4701916336871503145799281)
                ·
                  refine ⟨3526437252653627359349461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4701916336871503145799281 3526437252653627359349461)
                  ·
                    refine ⟨82650873109069391234753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3526437252653627359349461 82650873109069391234753)
                    ·
                      rfl

theorem cell22_241443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_241443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241443 prefixEnd_241443 := by exact prefixLift 241443
  have htrace : WordTrace (prefixWord ++ tailWord_241443) baseStart_241443 baseEnd_241443 := by
    simpa [prefixWord, tailWord_241443, baseEnd_241443] using wordTrace_append hprefix tailTrace_241443
  have hstable : (prefixWord ++ tailWord_241443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241443).length < 2 ^ (prefixWord ++ tailWord_241443).sum := by decide
  have hdescent : baseEnd_241443 < baseStart_241443 := by decide
  rcases family_descends (prefixWord ++ tailWord_241443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241554 : List Nat := [3, 2, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_241554 : Nat := 118140960795 + 241554 * 2 ^ 59
def prefixEnd_241554 : Nat := 4983230072969 + 3 ^ 40 * 241554 * 2
def baseEnd_241554 : Nat := 82688870677502101709413

theorem tailTrace_241554 : CollatzResearch.WordTrace tailWord_241554 prefixEnd_241554 82688870677502101709413 := by
  unfold tailWord_241554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2202549541724646745974929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5873465444599057989266477 2202549541724646745974929)
  ·
    refine ⟨1651912156293485059481197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2202549541724646745974929 1651912156293485059481197)
    ·
      refine ⟨619467058610056897305449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1651912156293485059481197 619467058610056897305449)
      ·
        refine ⟨464600293957542672979087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619467058610056897305449 464600293957542672979087)
        ·
          refine ⟨696900440936314009468631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464600293957542672979087 696900440936314009468631)
          ·
            refine ⟨1045350661404471014202947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696900440936314009468631 1045350661404471014202947)
            ·
              refine ⟨1568025992106706521304421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045350661404471014202947 1568025992106706521304421)
              ·
                refine ⟨294004873520007472744579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1568025992106706521304421 294004873520007472744579)
                ·
                  refine ⟨441007310280011209116869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294004873520007472744579 441007310280011209116869)
                  ·
                    refine ⟨82688870677502101709413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 441007310280011209116869 82688870677502101709413)
                    ·
                      rfl

theorem cell22_241554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_241554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241554 prefixEnd_241554 := by exact prefixLift 241554
  have htrace : WordTrace (prefixWord ++ tailWord_241554) baseStart_241554 baseEnd_241554 := by
    simpa [prefixWord, tailWord_241554, baseEnd_241554] using wordTrace_append hprefix tailTrace_241554
  have hstable : (prefixWord ++ tailWord_241554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241554).length < 2 ^ (prefixWord ++ tailWord_241554).sum := by decide
  have hdescent : baseEnd_241554 < baseStart_241554 := by decide
  rcases family_descends (prefixWord ++ tailWord_241554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241597 : List Nat := [1, 4, 1, 2, 3, 2, 2, 7]
def baseStart_241597 : Nat := 118140960795 + 241597 * 2 ^ 59
def prefixEnd_241597 : Nat := 4983230072969 + 3 ^ 40 * 241597 * 2
def baseEnd_241597 : Nat := 9189287828473813653809

theorem tailTrace_241597 : CollatzResearch.WordTrace tailWord_241597 prefixEnd_241597 9189287828473813653809 := by
  unfold tailWord_241597
  simp only [CollatzResearch.WordTrace]
  refine ⟨8811766505742805327715045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5874511003828536885143363 8811766505742805327715045)
  ·
    refine ⟨1652206219826775998946571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8811766505742805327715045 1652206219826775998946571)
    ·
      refine ⟨2478309329740163998419857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1652206219826775998946571 2478309329740163998419857)
      ·
        refine ⟨1858731997305122998814893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2478309329740163998419857 1858731997305122998814893)
        ·
          refine ⟨697024498989421124555585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1858731997305122998814893 697024498989421124555585)
          ·
            refine ⟨522768374242065843416689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697024498989421124555585 522768374242065843416689)
            ·
              refine ⟨392076280681549382562517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522768374242065843416689 392076280681549382562517)
              ·
                refine ⟨9189287828473813653809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 392076280681549382562517 9189287828473813653809)
                ·
                  rfl

theorem cell22_241597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 7].length) (baseStart_241597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241597 prefixEnd_241597 := by exact prefixLift 241597
  have htrace : WordTrace (prefixWord ++ tailWord_241597) baseStart_241597 baseEnd_241597 := by
    simpa [prefixWord, tailWord_241597, baseEnd_241597] using wordTrace_append hprefix tailTrace_241597
  have hstable : (prefixWord ++ tailWord_241597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241597).length < 2 ^ (prefixWord ++ tailWord_241597).sum := by decide
  have hdescent : baseEnd_241597 < baseStart_241597 := by decide
  rcases family_descends (prefixWord ++ tailWord_241597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241657 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 2, 5]
def baseStart_241657 : Nat := 118140960795 + 241657 * 2 ^ 59
def prefixEnd_241657 : Nat := 4983230072969 + 3 ^ 40 * 241657 * 2
def baseEnd_241657 : Nat := 82724129682444166384097

theorem tailTrace_241657 : CollatzResearch.WordTrace tailWord_241657 prefixEnd_241657 82724129682444166384097 := by
  unfold tailWord_241657
  simp only [CollatzResearch.WordTrace]
  refine ⟨8813954885525435574899225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5875969923683623716599483 8813954885525435574899225)
  ·
    refine ⟨6610466164144076681174419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8813954885525435574899225 6610466164144076681174419)
    ·
      refine ⟨9915699246216115021761629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6610466164144076681174419 9915699246216115021761629)
      ·
        refine ⟨3718387217331043133160611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9915699246216115021761629 3718387217331043133160611)
        ·
          refine ⟨5577580825996564699740917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3718387217331043133160611 5577580825996564699740917)
          ·
            refine ⟨522898202437177940600711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5577580825996564699740917 522898202437177940600711)
            ·
              refine ⟨784347303655766910901067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522898202437177940600711 784347303655766910901067)
              ·
                refine ⟨1176520955483650366351601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784347303655766910901067 1176520955483650366351601)
                ·
                  refine ⟨882390716612737774763701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1176520955483650366351601 882390716612737774763701)
                  ·
                    refine ⟨82724129682444166384097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 882390716612737774763701 82724129682444166384097)
                    ·
                      rfl

theorem cell22_241657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_241657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241657 prefixEnd_241657 := by exact prefixLift 241657
  have htrace : WordTrace (prefixWord ++ tailWord_241657) baseStart_241657 baseEnd_241657 := by
    simpa [prefixWord, tailWord_241657, baseEnd_241657] using wordTrace_append hprefix tailTrace_241657
  have hstable : (prefixWord ++ tailWord_241657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241657).length < 2 ^ (prefixWord ++ tailWord_241657).sum := by decide
  have hdescent : baseEnd_241657 < baseStart_241657 := by decide
  rcases family_descends (prefixWord ++ tailWord_241657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241672 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 3, 4]
def baseStart_241672 : Nat := 118140960795 + 241672 * 2 ^ 59
def prefixEnd_241672 : Nat := 4983230072969 + 3 ^ 40 * 241672 * 2
def baseEnd_241672 : Nat := 82729264488989127259051

theorem tailTrace_241672 : CollatzResearch.WordTrace tailWord_241672 prefixEnd_241672 82729264488989127259051 := by
  unfold tailWord_241672
  simp only [CollatzResearch.WordTrace]
  refine ⟨4407250990235546568347635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5876334653647395424463513 4407250990235546568347635)
  ·
    refine ⟨6610876485353319852521453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4407250990235546568347635 6610876485353319852521453)
    ·
      refine ⟨2479078682007494944695545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6610876485353319852521453 2479078682007494944695545)
      ·
        refine ⟨1859309011505621208521659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2479078682007494944695545 1859309011505621208521659)
        ·
          refine ⟨2788963517258431812782489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859309011505621208521659 2788963517258431812782489)
          ·
            refine ⟨2091722637943823859586867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2788963517258431812782489 2091722637943823859586867)
            ·
              refine ⟨3137583956915735789380301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091722637943823859586867 3137583956915735789380301)
              ·
                refine ⟨1176593983843400921017613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3137583956915735789380301 1176593983843400921017613)
                ·
                  refine ⟨441222743941275345381605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1176593983843400921017613 441222743941275345381605)
                  ·
                    refine ⟨82729264488989127259051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 441222743941275345381605 82729264488989127259051)
                    ·
                      rfl

theorem cell22_241672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_241672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241672 prefixEnd_241672 := by exact prefixLift 241672
  have htrace : WordTrace (prefixWord ++ tailWord_241672) baseStart_241672 baseEnd_241672 := by
    simpa [prefixWord, tailWord_241672, baseEnd_241672] using wordTrace_append hprefix tailTrace_241672
  have hstable : (prefixWord ++ tailWord_241672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241672).length < 2 ^ (prefixWord ++ tailWord_241672).sum := by decide
  have hdescent : baseEnd_241672 < baseStart_241672 := by decide
  rcases family_descends (prefixWord ++ tailWord_241672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241717 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_241717 : Nat := 118140960795 + 241717 * 2 ^ 59
def prefixEnd_241717 : Nat := 4983230072969 + 3 ^ 40 * 241717 * 2
def baseEnd_241717 : Nat := 82744668908624009883913

theorem tailTrace_241717 : CollatzResearch.WordTrace tailWord_241717 prefixEnd_241717 82744668908624009883913 := by
  unfold tailWord_241717
  simp only [CollatzResearch.WordTrace]
  refine ⟨8816143265308065822083405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5877428843538710548055603 8816143265308065822083405)
  ·
    refine ⟨3306053724490524683281277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8816143265308065822083405 3306053724490524683281277)
    ·
      refine ⟨1239770146683946756230479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3306053724490524683281277 1239770146683946756230479)
      ·
        refine ⟨1859655220025920134345719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1239770146683946756230479 1859655220025920134345719)
        ·
          refine ⟨2789482830038880201518579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859655220025920134345719 2789482830038880201518579)
          ·
            refine ⟨4184224245058320302277869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789482830038880201518579 4184224245058320302277869)
            ·
              refine ⟨1569084091896870113354201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4184224245058320302277869 1569084091896870113354201)
              ·
                refine ⟨1176813068922652585015651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569084091896870113354201 1176813068922652585015651)
                ·
                  refine ⟨1765219603383978877523477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176813068922652585015651 1765219603383978877523477)
                  ·
                    refine ⟨82744668908624009883913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1765219603383978877523477 82744668908624009883913)
                    ·
                      rfl

theorem cell22_241717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_241717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241717 prefixEnd_241717 := by exact prefixLift 241717
  have htrace : WordTrace (prefixWord ++ tailWord_241717) baseStart_241717 baseEnd_241717 := by
    simpa [prefixWord, tailWord_241717, baseEnd_241717] using wordTrace_append hprefix tailTrace_241717
  have hstable : (prefixWord ++ tailWord_241717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241717).length < 2 ^ (prefixWord ++ tailWord_241717).sum := by decide
  have hdescent : baseEnd_241717 < baseStart_241717 := by decide
  rcases family_descends (prefixWord ++ tailWord_241717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241719 : List Nat := [1, 1, 3, 1, 2, 2, 2, 5, 2, 3]
def baseStart_241719 : Nat := 118140960795 + 241719 * 2 ^ 59
def prefixEnd_241719 : Nat := 4983230072969 + 3 ^ 40 * 241719 * 2
def baseEnd_241719 : Nat := 82745353549496671333907

theorem tailTrace_241719 : CollatzResearch.WordTrace tailWord_241719 prefixEnd_241719 82745353549496671333907 := by
  unfold tailWord_241719
  simp only [CollatzResearch.WordTrace]
  refine ⟨8816216211300820163656211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5877477474200546775770807 8816216211300820163656211)
  ·
    refine ⟨13224324316951230245484317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8816216211300820163656211 13224324316951230245484317)
    ·
      refine ⟨4959121618856711342056619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13224324316951230245484317 4959121618856711342056619)
      ·
        refine ⟨7438682428285067013084929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4959121618856711342056619 7438682428285067013084929)
        ·
          refine ⟨5579011821213800259813697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7438682428285067013084929 5579011821213800259813697)
          ·
            refine ⟨4184258865910350194860273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5579011821213800259813697 4184258865910350194860273)
            ·
              refine ⟨3138194149432762646145205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4184258865910350194860273 3138194149432762646145205)
              ·
                refine ⟨294205701509321498076113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3138194149432762646145205 294205701509321498076113)
                ·
                  refine ⟨220654276131991123557085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294205701509321498076113 220654276131991123557085)
                  ·
                    refine ⟨82745353549496671333907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 220654276131991123557085 82745353549496671333907)
                    ·
                      rfl

theorem cell22_241719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_241719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241719 prefixEnd_241719 := by exact prefixLift 241719
  have htrace : WordTrace (prefixWord ++ tailWord_241719) baseStart_241719 baseEnd_241719 := by
    simpa [prefixWord, tailWord_241719, baseEnd_241719] using wordTrace_append hprefix tailTrace_241719
  have hstable : (prefixWord ++ tailWord_241719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241719).length < 2 ^ (prefixWord ++ tailWord_241719).sum := by decide
  have hdescent : baseEnd_241719 < baseStart_241719 := by decide
  rcases family_descends (prefixWord ++ tailWord_241719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241770 : List Nat := [3, 1, 3, 2, 3, 2, 2, 1, 2, 3]
def baseStart_241770 : Nat := 118140960795 + 241770 * 2 ^ 59
def prefixEnd_241770 : Nat := 4983230072969 + 3 ^ 40 * 241770 * 2
def baseEnd_241770 : Nat := 82762811891749538308751

theorem tailTrace_241770 : CollatzResearch.WordTrace tailWord_241770 prefixEnd_241770 82762811891749538308751 := by
  unfold tailWord_241770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2204519083529013968440691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5878717556077370582508509 2204519083529013968440691)
  ·
    refine ⟨3306778625293520952661037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2204519083529013968440691 3306778625293520952661037)
    ·
      refine ⟨1240041984485070357247889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3306778625293520952661037 1240041984485070357247889)
      ·
        refine ⟨930031488363802767935917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1240041984485070357247889 930031488363802767935917)
        ·
          refine ⟨348761808136426037975969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 930031488363802767935917 348761808136426037975969)
          ·
            refine ⟨261571356102319528481977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348761808136426037975969 261571356102319528481977)
            ·
              refine ⟨196178517076739646361483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261571356102319528481977 196178517076739646361483)
              ·
                refine ⟨294267775615109469542225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196178517076739646361483 294267775615109469542225)
                ·
                  refine ⟨220700831711332102156669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294267775615109469542225 220700831711332102156669)
                  ·
                    refine ⟨82762811891749538308751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 220700831711332102156669 82762811891749538308751)
                    ·
                      rfl

theorem cell22_241770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_241770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241770 prefixEnd_241770 := by exact prefixLift 241770
  have htrace : WordTrace (prefixWord ++ tailWord_241770) baseStart_241770 baseEnd_241770 := by
    simpa [prefixWord, tailWord_241770, baseEnd_241770] using wordTrace_append hprefix tailTrace_241770
  have hstable : (prefixWord ++ tailWord_241770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241770).length < 2 ^ (prefixWord ++ tailWord_241770).sum := by decide
  have hdescent : baseEnd_241770 < baseStart_241770 := by decide
  rcases family_descends (prefixWord ++ tailWord_241770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241792 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 4, 5]
def baseStart_241792 : Nat := 118140960795 + 241792 * 2 ^ 59
def prefixEnd_241792 : Nat := 4983230072969 + 3 ^ 40 * 241792 * 2
def baseEnd_241792 : Nat := 82770342941348814258683

theorem tailTrace_241792 : CollatzResearch.WordTrace tailWord_241792 prefixEnd_241792 82770342941348814258683 := by
  unfold tailWord_241792
  simp only [CollatzResearch.WordTrace]
  refine ⟨4409439370018176815531815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5879252493357569087375753 4409439370018176815531815)
  ·
    refine ⟨6614159055027265223297723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4409439370018176815531815 6614159055027265223297723)
    ·
      refine ⟨9921238582540897834946585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6614159055027265223297723 9921238582540897834946585)
      ·
        refine ⟨7440928936905673376209939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9921238582540897834946585 7440928936905673376209939)
        ·
          refine ⟨11161393405358510064314909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7440928936905673376209939 11161393405358510064314909)
          ·
            refine ⟨4185522527009441274118091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11161393405358510064314909 4185522527009441274118091)
            ·
              refine ⟨6278283790514161911177137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4185522527009441274118091 6278283790514161911177137)
              ·
                refine ⟨4708712842885621433382853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6278283790514161911177137 4708712842885621433382853)
                ·
                  refine ⟨882883658041054018759285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4708712842885621433382853 882883658041054018759285)
                  ·
                    refine ⟨82770342941348814258683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 882883658041054018759285 82770342941348814258683)
                    ·
                      rfl

theorem cell22_241792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_241792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241792 prefixEnd_241792 := by exact prefixLift 241792
  have htrace : WordTrace (prefixWord ++ tailWord_241792) baseStart_241792 baseEnd_241792 := by
    simpa [prefixWord, tailWord_241792, baseEnd_241792] using wordTrace_append hprefix tailTrace_241792
  have hstable : (prefixWord ++ tailWord_241792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241792).length < 2 ^ (prefixWord ++ tailWord_241792).sum := by decide
  have hdescent : baseEnd_241792 < baseStart_241792 := by decide
  rcases family_descends (prefixWord ++ tailWord_241792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241824 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 3, 4]
def baseStart_241824 : Nat := 118140960795 + 241824 * 2 ^ 59
def prefixEnd_241824 : Nat := 4983230072969 + 3 ^ 40 * 241824 * 2
def baseEnd_241824 : Nat := 82781297195311397458585

theorem tailTrace_241824 : CollatzResearch.WordTrace tailWord_241824 prefixEnd_241824 82781297195311397458585 := by
  unfold tailWord_241824
  simp only [CollatzResearch.WordTrace]
  refine ⟨4410022937960211548114263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5880030583946948730819017 4410022937960211548114263)
  ·
    refine ⟨6615034406940317322171395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4410022937960211548114263 6615034406940317322171395)
    ·
      refine ⟨9922551610410475983257093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6615034406940317322171395 9922551610410475983257093)
      ·
        refine ⟨1860478426951964246860705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9922551610410475983257093 1860478426951964246860705)
        ·
          refine ⟨1395358820213973185145529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1860478426951964246860705 1395358820213973185145529)
          ·
            refine ⟨1046519115160479888859147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1395358820213973185145529 1046519115160479888859147)
            ·
              refine ⟨1569778672740719833288721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046519115160479888859147 1569778672740719833288721)
              ·
                refine ⟨1177334004555539874966541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569778672740719833288721 1177334004555539874966541)
                ·
                  refine ⟨441500251708327453112453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177334004555539874966541 441500251708327453112453)
                  ·
                    refine ⟨82781297195311397458585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 441500251708327453112453 82781297195311397458585)
                    ·
                      rfl

theorem cell22_241824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_241824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241824 prefixEnd_241824 := by exact prefixLift 241824
  have htrace : WordTrace (prefixWord ++ tailWord_241824) baseStart_241824 baseEnd_241824 := by
    simpa [prefixWord, tailWord_241824, baseEnd_241824] using wordTrace_append hprefix tailTrace_241824
  have hstable : (prefixWord ++ tailWord_241824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241824).length < 2 ^ (prefixWord ++ tailWord_241824).sum := by decide
  have hdescent : baseEnd_241824 < baseStart_241824 := by decide
  rcases family_descends (prefixWord ++ tailWord_241824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241826 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_241826 : Nat := 118140960795 + 241826 * 2 ^ 59
def prefixEnd_241826 : Nat := 4983230072969 + 3 ^ 40 * 241826 * 2
def baseEnd_241826 : Nat := 82781981836184058908579

theorem tailTrace_241826 : CollatzResearch.WordTrace tailWord_241826 prefixEnd_241826 82781981836184058908579 := by
  unfold tailWord_241826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2205029705478294359450333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5880079214608784958534221 2205029705478294359450333)
  ·
    refine ⟨826886139554360384793875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2205029705478294359450333 826886139554360384793875)
    ·
      refine ⟨1240329209331540577190813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 826886139554360384793875 1240329209331540577190813)
      ·
        refine ⟨465123453499327716446555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1240329209331540577190813 465123453499327716446555)
        ·
          refine ⟨697685180248991574669833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465123453499327716446555 697685180248991574669833)
          ·
            refine ⟨523263885186743681002375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697685180248991574669833 523263885186743681002375)
            ·
              refine ⟨784895827780115521503563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523263885186743681002375 784895827780115521503563)
              ·
                refine ⟨1177343741670173282255345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784895827780115521503563 1177343741670173282255345)
                ·
                  refine ⟨883007806252629961691509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1177343741670173282255345 883007806252629961691509)
                  ·
                    refine ⟨82781981836184058908579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 883007806252629961691509 82781981836184058908579)
                    ·
                      rfl

theorem cell22_241826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_241826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241826 prefixEnd_241826 := by exact prefixLift 241826
  have htrace : WordTrace (prefixWord ++ tailWord_241826) baseStart_241826 baseEnd_241826 := by
    simpa [prefixWord, tailWord_241826, baseEnd_241826] using wordTrace_append hprefix tailTrace_241826
  have hstable : (prefixWord ++ tailWord_241826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241826).length < 2 ^ (prefixWord ++ tailWord_241826).sum := by decide
  have hdescent : baseEnd_241826 < baseStart_241826 := by decide
  rcases family_descends (prefixWord ++ tailWord_241826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241856 : List Nat := [2, 1, 1, 2, 5, 1, 1, 5, 4]
def baseStart_241856 : Nat := 118140960795 + 241856 * 2 ^ 59
def prefixEnd_241856 : Nat := 4983230072969 + 3 ^ 40 * 241856 * 2
def baseEnd_241856 : Nat := 27597417149757993552829

theorem tailTrace_241856 : CollatzResearch.WordTrace tailWord_241856 prefixEnd_241856 27597417149757993552829 := by
  unfold tailWord_241856
  simp only [CollatzResearch.WordTrace]
  refine ⟨4410606505902246280696711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5880808674536328374262281 4410606505902246280696711)
  ·
    refine ⟨6615909758853369421045067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4410606505902246280696711 6615909758853369421045067)
    ·
      refine ⟨9923864638280054131567601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6615909758853369421045067 9923864638280054131567601)
      ·
        refine ⟨7442898478710040598675701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9923864638280054131567601 7442898478710040598675701)
        ·
          refine ⟨697771732379066306125847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7442898478710040598675701 697771732379066306125847)
          ·
            refine ⟨1046657598568599459188771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697771732379066306125847 1046657598568599459188771)
            ·
              refine ⟨1569986397852899188783157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046657598568599459188771 1569986397852899188783157)
              ·
                refine ⟨147186224798709298948421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1569986397852899188783157 147186224798709298948421)
                ·
                  refine ⟨27597417149757993552829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147186224798709298948421 27597417149757993552829)
                  ·
                    rfl

theorem cell22_241856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 4].length) (baseStart_241856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241856 prefixEnd_241856 := by exact prefixLift 241856
  have htrace : WordTrace (prefixWord ++ tailWord_241856) baseStart_241856 baseEnd_241856 := by
    simpa [prefixWord, tailWord_241856, baseEnd_241856] using wordTrace_append hprefix tailTrace_241856
  have hstable : (prefixWord ++ tailWord_241856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241856).length < 2 ^ (prefixWord ++ tailWord_241856).sum := by decide
  have hdescent : baseEnd_241856 < baseStart_241856 := by decide
  rcases family_descends (prefixWord ++ tailWord_241856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241867 : List Nat := [1, 1, 1, 1, 3, 2, 13]
def baseStart_241867 : Nat := 118140960795 + 241867 * 2 ^ 59
def prefixEnd_241867 : Nat := 4983230072969 + 3 ^ 40 * 241867 * 2
def baseEnd_241867 : Nat := 3066519147187911801239

theorem tailTrace_241867 : CollatzResearch.WordTrace tailWord_241867 prefixEnd_241867 3066519147187911801239 := by
  unfold tailWord_241867
  simp only [CollatzResearch.WordTrace]
  refine ⟨8821614214764641440043855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5881076143176427626695903 8821614214764641440043855)
  ·
    refine ⟨13232421322146962160065783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8821614214764641440043855 13232421322146962160065783)
    ·
      refine ⟨19848631983220443240098675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13232421322146962160065783 19848631983220443240098675)
      ·
        refine ⟨29772947974830664860148013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19848631983220443240098675 29772947974830664860148013)
        ·
          refine ⟨11164855490561499322555505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29772947974830664860148013 11164855490561499322555505)
          ·
            refine ⟨8373641617921124491916629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11164855490561499322555505 8373641617921124491916629)
            ·
              refine ⟨3066519147187911801239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 8373641617921124491916629 3066519147187911801239)
              ·
                rfl

theorem cell22_241867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 13].length) (baseStart_241867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241867 prefixEnd_241867 := by exact prefixLift 241867
  have htrace : WordTrace (prefixWord ++ tailWord_241867) baseStart_241867 baseEnd_241867 := by
    simpa [prefixWord, tailWord_241867, baseEnd_241867] using wordTrace_append hprefix tailTrace_241867
  have hstable : (prefixWord ++ tailWord_241867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241867).length < 2 ^ (prefixWord ++ tailWord_241867).sum := by decide
  have hdescent : baseEnd_241867 < baseStart_241867 := by decide
  rcases family_descends (prefixWord ++ tailWord_241867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241888 : List Nat := [2, 1, 1, 3, 1, 3, 5, 1, 2, 3]
def baseStart_241888 : Nat := 118140960795 + 241888 * 2 ^ 59
def prefixEnd_241888 : Nat := 4983230072969 + 3 ^ 40 * 241888 * 2
def baseEnd_241888 : Nat := 82803205703236563858389

theorem tailTrace_241888 : CollatzResearch.WordTrace tailWord_241888 prefixEnd_241888 82803205703236563858389 := by
  unfold tailWord_241888
  simp only [CollatzResearch.WordTrace]
  refine ⟨4411190073844281013279159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5881586765125708017705545 4411190073844281013279159)
  ·
    refine ⟨6616785110766421519918739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4411190073844281013279159 6616785110766421519918739)
    ·
      refine ⟨9925177666149632279878109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6616785110766421519918739 9925177666149632279878109)
      ·
        refine ⟨3721941624806112104954291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9925177666149632279878109 3721941624806112104954291)
        ·
          refine ⟨5582912437209168157431437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3721941624806112104954291 5582912437209168157431437)
          ·
            refine ⟨2093592163953438059036789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5582912437209168157431437 2093592163953438059036789)
            ·
              refine ⟨196274265370634818034699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2093592163953438059036789 196274265370634818034699)
              ·
                refine ⟨294411398055952227052049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196274265370634818034699 294411398055952227052049)
                ·
                  refine ⟨220808548541964170289037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294411398055952227052049 220808548541964170289037)
                  ·
                    refine ⟨82803205703236563858389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 220808548541964170289037 82803205703236563858389)
                    ·
                      rfl

theorem cell22_241888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 2, 3].length) (baseStart_241888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241888 prefixEnd_241888 := by exact prefixLift 241888
  have htrace : WordTrace (prefixWord ++ tailWord_241888) baseStart_241888 baseEnd_241888 := by
    simpa [prefixWord, tailWord_241888, baseEnd_241888] using wordTrace_append hprefix tailTrace_241888
  have hstable : (prefixWord ++ tailWord_241888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241888).length < 2 ^ (prefixWord ++ tailWord_241888).sum := by decide
  have hdescent : baseEnd_241888 < baseStart_241888 := by decide
  rcases family_descends (prefixWord ++ tailWord_241888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241901 : List Nat := [1, 5, 1, 2, 3, 1, 1, 8]
def baseStart_241901 : Nat := 118140960795 + 241901 * 2 ^ 59
def prefixEnd_241901 : Nat := 4983230072969 + 3 ^ 40 * 241901 * 2
def baseEnd_241901 : Nat := 9200850652100984809261

theorem tailTrace_241901 : CollatzResearch.WordTrace tailWord_241901 prefixEnd_241901 9200850652100984809261 := by
  unfold tailWord_241901
  simp only [CollatzResearch.WordTrace]
  refine ⟨8822854296641465246781557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5881902864427643497854371 8822854296641465246781557)
  ·
    refine ⟨827142590310137366885771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8822854296641465246781557 827142590310137366885771)
    ·
      refine ⟨1240713885465206050328657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 827142590310137366885771 1240713885465206050328657)
      ·
        refine ⟨930535414098904537746493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1240713885465206050328657 930535414098904537746493)
        ·
          refine ⟨348950780287089201654935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 930535414098904537746493 348950780287089201654935)
          ·
            refine ⟨523426170430633802482403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348950780287089201654935 523426170430633802482403)
            ·
              refine ⟨785139255645950703723605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523426170430633802482403 785139255645950703723605)
              ·
                refine ⟨9200850652100984809261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 785139255645950703723605 9200850652100984809261)
                ·
                  rfl

theorem cell22_241901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 8].length) (baseStart_241901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241901 prefixEnd_241901 := by exact prefixLift 241901
  have htrace : WordTrace (prefixWord ++ tailWord_241901) baseStart_241901 baseEnd_241901 := by
    simpa [prefixWord, tailWord_241901, baseEnd_241901] using wordTrace_append hprefix tailTrace_241901
  have hstable : (prefixWord ++ tailWord_241901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241901).length < 2 ^ (prefixWord ++ tailWord_241901).sum := by decide
  have hdescent : baseEnd_241901 < baseStart_241901 := by decide
  rcases family_descends (prefixWord ++ tailWord_241901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241929 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 7]
def baseStart_241929 : Nat := 118140960795 + 241929 * 2 ^ 59
def prefixEnd_241929 : Nat := 4983230072969 + 3 ^ 40 * 241929 * 2
def baseEnd_241929 : Nat := 27605746947042041194421

theorem tailTrace_241929 : CollatzResearch.WordTrace tailWord_241929 prefixEnd_241929 27605746947042041194421 := by
  unfold tailWord_241929
  simp only [CollatzResearch.WordTrace]
  refine ⟨8823875540540026028800841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5882583693693350685867227 8823875540540026028800841)
  ·
    refine ⟨6617906655405019521600631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8823875540540026028800841 6617906655405019521600631)
    ·
      refine ⟨9926859983107529282400947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6617906655405019521600631 9926859983107529282400947)
      ·
        refine ⟨14890289974661293923601421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9926859983107529282400947 14890289974661293923601421)
        ·
          refine ⟨5583858740497985221350533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14890289974661293923601421 5583858740497985221350533)
          ·
            refine ⟨1046973513843372229003225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5583858740497985221350533 1046973513843372229003225)
            ·
              refine ⟨785230135382529171752419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046973513843372229003225 785230135382529171752419)
              ·
                refine ⟨1177845203073793757628629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785230135382529171752419 1177845203073793757628629)
                ·
                  refine ⟨27605746947042041194421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1177845203073793757628629 27605746947042041194421)
                  ·
                    rfl

theorem cell22_241929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_241929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241929 prefixEnd_241929 := by exact prefixLift 241929
  have htrace : WordTrace (prefixWord ++ tailWord_241929) baseStart_241929 baseEnd_241929 := by
    simpa [prefixWord, tailWord_241929, baseEnd_241929] using wordTrace_append hprefix tailTrace_241929
  have hstable : (prefixWord ++ tailWord_241929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241929).length < 2 ^ (prefixWord ++ tailWord_241929).sum := by decide
  have hdescent : baseEnd_241929 < baseStart_241929 := by decide
  rcases family_descends (prefixWord ++ tailWord_241929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241944 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 1, 7]
def baseStart_241944 : Nat := 118140960795 + 241944 * 2 ^ 59
def prefixEnd_241944 : Nat := 4983230072969 + 3 ^ 40 * 241944 * 2
def baseEnd_241944 : Nat := 82822375647671084458217

theorem tailTrace_241944 : CollatzResearch.WordTrace tailWord_241944 prefixEnd_241944 82822375647671084458217 := by
  unfold tailWord_241944
  simp only [CollatzResearch.WordTrace]
  refine ⟨4412211317742841795298443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5882948423657122393731257 4412211317742841795298443)
  ·
    refine ⟨6618316976614262692947665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4412211317742841795298443 6618316976614262692947665)
    ·
      refine ⟨4963737732460697019710749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6618316976614262692947665 4963737732460697019710749)
      ·
        refine ⟨1861401649672761382391531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4963737732460697019710749 1861401649672761382391531)
        ·
          refine ⟨2792102474509142073587297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861401649672761382391531 2792102474509142073587297)
          ·
            refine ⟨2094076855881856555190473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2792102474509142073587297 2094076855881856555190473)
            ·
              refine ⟨1570557641911392416392855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2094076855881856555190473 1570557641911392416392855)
              ·
                refine ⟨2355836462867088624589283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570557641911392416392855 2355836462867088624589283)
                ·
                  refine ⟨3533754694300632936883925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355836462867088624589283 3533754694300632936883925)
                  ·
                    refine ⟨82822375647671084458217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3533754694300632936883925 82822375647671084458217)
                    ·
                      rfl

theorem cell22_241944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_241944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241944 prefixEnd_241944 := by exact prefixLift 241944
  have htrace : WordTrace (prefixWord ++ tailWord_241944) baseStart_241944 baseEnd_241944 := by
    simpa [prefixWord, tailWord_241944, baseEnd_241944] using wordTrace_append hprefix tailTrace_241944
  have hstable : (prefixWord ++ tailWord_241944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241944).length < 2 ^ (prefixWord ++ tailWord_241944).sum := by decide
  have hdescent : baseEnd_241944 < baseStart_241944 := by decide
  rcases family_descends (prefixWord ++ tailWord_241944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241976 : List Nat := [2, 1, 2, 1, 3, 1, 2, 5, 1, 4]
def baseStart_241976 : Nat := 118140960795 + 241976 * 2 ^ 59
def prefixEnd_241976 : Nat := 4983230072969 + 3 ^ 40 * 241976 * 2
def baseEnd_241976 : Nat := 82833329901633667658119

theorem tailTrace_241976 : CollatzResearch.WordTrace tailWord_241976 prefixEnd_241976 82833329901633667658119 := by
  unfold tailWord_241976
  simp only [CollatzResearch.WordTrace]
  refine ⟨4412794885684876527880891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5883726514246502037174521 4412794885684876527880891)
  ·
    refine ⟨6619192328527314791821337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4412794885684876527880891 6619192328527314791821337)
    ·
      refine ⟨4964394246395486093866003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6619192328527314791821337 4964394246395486093866003)
      ·
        refine ⟨7446591369593229140799005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4964394246395486093866003 7446591369593229140799005)
        ·
          refine ⟨2792471763597460927799627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7446591369593229140799005 2792471763597460927799627)
          ·
            refine ⟨4188707645396191391699441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792471763597460927799627 4188707645396191391699441)
            ·
              refine ⟨3141530734047143543774581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4188707645396191391699441 3141530734047143543774581)
              ·
                refine ⟨294518506316919707228867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3141530734047143543774581 294518506316919707228867)
                ·
                  refine ⟨441777759475379560843301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294518506316919707228867 441777759475379560843301)
                  ·
                    refine ⟨82833329901633667658119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 441777759475379560843301 82833329901633667658119)
                    ·
                      rfl

theorem cell22_241976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_241976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_241976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_241976 prefixEnd_241976 := by exact prefixLift 241976
  have htrace : WordTrace (prefixWord ++ tailWord_241976) baseStart_241976 baseEnd_241976 := by
    simpa [prefixWord, tailWord_241976, baseEnd_241976] using wordTrace_append hprefix tailTrace_241976
  have hstable : (prefixWord ++ tailWord_241976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241976).length < 2 ^ (prefixWord ++ tailWord_241976).sum := by decide
  have hdescent : baseEnd_241976 < baseStart_241976 := by decide
  rcases family_descends (prefixWord ++ tailWord_241976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242021 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_242021 : Nat := 118140960795 + 242021 * 2 ^ 59
def prefixEnd_242021 : Nat := 4983230072969 + 3 ^ 40 * 242021 * 2
def baseEnd_242021 : Nat := 82848734321268550282981

theorem tailTrace_242021 : CollatzResearch.WordTrace tailWord_242021 prefixEnd_242021 82848734321268550282981 := by
  unfold tailWord_242021
  simp only [CollatzResearch.WordTrace]
  refine ⟨8827231056206725741149917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5884820704137817160766611 8827231056206725741149917)
  ·
    refine ⟨3310211646077522152931219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8827231056206725741149917 3310211646077522152931219)
    ·
      refine ⟨4965317469116283229396829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3310211646077522152931219 4965317469116283229396829)
      ·
        refine ⟨1861994050918606211023811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4965317469116283229396829 1861994050918606211023811)
        ·
          refine ⟨2792991076377909316535717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861994050918606211023811 2792991076377909316535717)
          ·
            refine ⟨523685826820857996850447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2792991076377909316535717 523685826820857996850447)
            ·
              refine ⟨785528740231286995275671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523685826820857996850447 785528740231286995275671)
              ·
                refine ⟨1178293110346930492913507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785528740231286995275671 1178293110346930492913507)
                ·
                  refine ⟨1767439665520395739370261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178293110346930492913507 1767439665520395739370261)
                  ·
                    refine ⟨82848734321268550282981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1767439665520395739370261 82848734321268550282981)
                    ·
                      rfl

theorem cell22_242021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_242021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242021 prefixEnd_242021 := by exact prefixLift 242021
  have htrace : WordTrace (prefixWord ++ tailWord_242021) baseStart_242021 baseEnd_242021 := by
    simpa [prefixWord, tailWord_242021, baseEnd_242021] using wordTrace_append hprefix tailTrace_242021
  have hstable : (prefixWord ++ tailWord_242021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242021).length < 2 ^ (prefixWord ++ tailWord_242021).sum := by decide
  have hdescent : baseEnd_242021 < baseStart_242021 := by decide
  rcases family_descends (prefixWord ++ tailWord_242021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242126 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_242126 : Nat := 118140960795 + 242126 * 2 ^ 59
def prefixEnd_242126 : Nat := 4983230072969 + 3 ^ 40 * 242126 * 2
def baseEnd_242126 : Nat := 27628225989027758802553

theorem tailTrace_242126 : CollatzResearch.WordTrace tailWord_242126 prefixEnd_242126 27628225989027758802553 := by
  unfold tailWord_242126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103882590103291084215279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5887373813884219115814821 1103882590103291084215279)
  ·
    refine ⟨1655823885154936626322919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1103882590103291084215279 1655823885154936626322919)
    ·
      refine ⟨2483735827732404939484379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655823885154936626322919 2483735827732404939484379)
      ·
        refine ⟨3725603741598607409226569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2483735827732404939484379 3725603741598607409226569)
        ·
          refine ⟨2794202806198955556919927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3725603741598607409226569 2794202806198955556919927)
          ·
            refine ⟨4191304209298433335379891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794202806198955556919927 4191304209298433335379891)
            ·
              refine ⟨6286956313947650003069837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191304209298433335379891 6286956313947650003069837)
              ·
                refine ⟨2357608617730368751151189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6286956313947650003069837 2357608617730368751151189)
                ·
                  refine ⟨27628225989027758802553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2357608617730368751151189 27628225989027758802553)
                  ·
                    rfl

theorem cell22_242126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_242126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242126 prefixEnd_242126 := by exact prefixLift 242126
  have htrace : WordTrace (prefixWord ++ tailWord_242126) baseStart_242126 baseEnd_242126 := by
    simpa [prefixWord, tailWord_242126, baseEnd_242126] using wordTrace_append hprefix tailTrace_242126
  have hstable : (prefixWord ++ tailWord_242126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242126).length < 2 ^ (prefixWord ++ tailWord_242126).sum := by decide
  have hdescent : baseEnd_242126 < baseStart_242126 := by decide
  rcases family_descends (prefixWord ++ tailWord_242126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242145 : List Nat := [1, 2, 3, 1, 2, 2, 5, 1, 1, 4]
def baseStart_242145 : Nat := 118140960795 + 242145 * 2 ^ 59
def prefixEnd_242145 : Nat := 4983230072969 + 3 ^ 40 * 242145 * 2
def baseEnd_242145 : Nat := 82891182055373560182601

theorem tailTrace_242145 : CollatzResearch.WordTrace tailWord_242145 prefixEnd_242145 82891182055373560182601 := by
  unfold tailWord_242145
  simp only [CollatzResearch.WordTrace]
  refine ⟨8831753707757494918663889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5887835805171663279109259 8831753707757494918663889)
  ·
    refine ⟨6623815280818121188997917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8831753707757494918663889 6623815280818121188997917)
    ·
      refine ⟨2483930730306795445874219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6623815280818121188997917 2483930730306795445874219)
      ·
        refine ⟨3725896095460193168811329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2483930730306795445874219 3725896095460193168811329)
        ·
          refine ⟨2794422071595144876608497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3725896095460193168811329 2794422071595144876608497)
          ·
            refine ⟨2095816553696358657456373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2794422071595144876608497 2095816553696358657456373)
            ·
              refine ⟨196482801909033624136535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2095816553696358657456373 196482801909033624136535)
              ·
                refine ⟨294724202863550436204803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196482801909033624136535 294724202863550436204803)
                ·
                  refine ⟨442086304295325654307205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294724202863550436204803 442086304295325654307205)
                  ·
                    refine ⟨82891182055373560182601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 442086304295325654307205 82891182055373560182601)
                    ·
                      rfl

theorem cell22_242145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_242145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242145 prefixEnd_242145 := by exact prefixLift 242145
  have htrace : WordTrace (prefixWord ++ tailWord_242145) baseStart_242145 baseEnd_242145 := by
    simpa [prefixWord, tailWord_242145, baseEnd_242145] using wordTrace_append hprefix tailTrace_242145
  have hstable : (prefixWord ++ tailWord_242145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242145).length < 2 ^ (prefixWord ++ tailWord_242145).sum := by decide
  have hdescent : baseEnd_242145 < baseStart_242145 := by decide
  rcases family_descends (prefixWord ++ tailWord_242145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242190 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_242190 : Nat := 118140960795 + 242190 * 2 ^ 59
def prefixEnd_242190 : Nat := 4983230072969 + 3 ^ 40 * 242190 * 2
def baseEnd_242190 : Nat := 82906586475008442807463

theorem tailTrace_242190 : CollatzResearch.WordTrace tailWord_242190 prefixEnd_242190 82906586475008442807463 := by
  unfold tailWord_242190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104174374074308450506503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5888929995062978402701349 1104174374074308450506503)
  ·
    refine ⟨1656261561111462675759755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1104174374074308450506503 1656261561111462675759755)
    ·
      refine ⟨2484392341667194013639633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1656261561111462675759755 2484392341667194013639633)
      ·
        refine ⟨1863294256250395510229725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2484392341667194013639633 1863294256250395510229725)
        ·
          refine ⟨698735346093898316336147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1863294256250395510229725 698735346093898316336147)
          ·
            refine ⟨1048103019140847474504221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698735346093898316336147 1048103019140847474504221)
            ·
              refine ⟨393038632177817802939083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1048103019140847474504221 393038632177817802939083)
              ·
                refine ⟨589557948266726704408625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393038632177817802939083 589557948266726704408625)
                ·
                  refine ⟨442168461200045028306469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589557948266726704408625 442168461200045028306469)
                  ·
                    refine ⟨82906586475008442807463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 442168461200045028306469 82906586475008442807463)
                    ·
                      rfl

theorem cell22_242190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_242190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242190 prefixEnd_242190 := by exact prefixLift 242190
  have htrace : WordTrace (prefixWord ++ tailWord_242190) baseStart_242190 baseEnd_242190 := by
    simpa [prefixWord, tailWord_242190, baseEnd_242190] using wordTrace_append hprefix tailTrace_242190
  have hstable : (prefixWord ++ tailWord_242190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242190).length < 2 ^ (prefixWord ++ tailWord_242190).sum := by decide
  have hdescent : baseEnd_242190 < baseStart_242190 := by decide
  rcases family_descends (prefixWord ++ tailWord_242190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242201 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 4, 6]
def baseStart_242201 : Nat := 118140960795 + 242201 * 2 ^ 59
def prefixEnd_242201 : Nat := 4983230072969 + 3 ^ 40 * 242201 * 2
def baseEnd_242201 : Nat := 82910351999808080782429

theorem tailTrace_242201 : CollatzResearch.WordTrace tailWord_242201 prefixEnd_242201 82910351999808080782429 := by
  unfold tailWord_242201
  simp only [CollatzResearch.WordTrace]
  refine ⟨8833796195554616482702457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5889197463703077655134971 8833796195554616482702457)
  ·
    refine ⟨6625347146665962362026843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8833796195554616482702457 6625347146665962362026843)
    ·
      refine ⟨9938020719998943543040265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6625347146665962362026843 9938020719998943543040265)
      ·
        refine ⟨7453515539999207657280199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9938020719998943543040265 7453515539999207657280199)
        ·
          refine ⟨11180273309998811485920299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7453515539999207657280199 11180273309998811485920299)
          ·
            refine ⟨16770409964998217228880449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11180273309998811485920299 16770409964998217228880449)
            ·
              refine ⟨12577807473748662921660337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16770409964998217228880449 12577807473748662921660337)
              ·
                refine ⟨9433355605311497191245253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12577807473748662921660337 9433355605311497191245253)
                ·
                  refine ⟨1768754175995905723358485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9433355605311497191245253 1768754175995905723358485)
                  ·
                    refine ⟨82910351999808080782429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1768754175995905723358485 82910351999808080782429)
                    ·
                      rfl

theorem cell22_242201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_242201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242201 prefixEnd_242201 := by exact prefixLift 242201
  have htrace : WordTrace (prefixWord ++ tailWord_242201) baseStart_242201 baseEnd_242201 := by
    simpa [prefixWord, tailWord_242201, baseEnd_242201] using wordTrace_append hprefix tailTrace_242201
  have hstable : (prefixWord ++ tailWord_242201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242201).length < 2 ^ (prefixWord ++ tailWord_242201).sum := by decide
  have hdescent : baseEnd_242201 < baseStart_242201 := by decide
  rcases family_descends (prefixWord ++ tailWord_242201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242297 : List Nat := [1, 2, 1, 3, 3, 4, 1, 2, 1, 4]
def baseStart_242297 : Nat := 118140960795 + 242297 * 2 ^ 59
def prefixEnd_242297 : Nat := 4983230072969 + 3 ^ 40 * 242297 * 2
def baseEnd_242297 : Nat := 82943214761695830382135

theorem tailTrace_242297 : CollatzResearch.WordTrace tailWord_242297 prefixEnd_242297 82943214761695830382135 := by
  unfold tailWord_242297
  simp only [CollatzResearch.WordTrace]
  refine ⟨8837297603206824878197145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5891531735471216585464763 8837297603206824878197145)
  ·
    refine ⟨6627973202405118658647859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8837297603206824878197145 6627973202405118658647859)
    ·
      refine ⟨9941959803607677987971789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6627973202405118658647859 9941959803607677987971789)
      ·
        refine ⟨3728234926352879245489421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9941959803607677987971789 3728234926352879245489421)
        ·
          refine ⟨1398088097382329717058533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3728234926352879245489421 1398088097382329717058533)
          ·
            refine ⟨262141518259186821948475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1398088097382329717058533 262141518259186821948475)
            ·
              refine ⟨393212277388780232922713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262141518259186821948475 393212277388780232922713)
              ·
                refine ⟨294909208041585174692035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393212277388780232922713 294909208041585174692035)
                ·
                  refine ⟨442363812062377762038053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294909208041585174692035 442363812062377762038053)
                  ·
                    refine ⟨82943214761695830382135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 442363812062377762038053 82943214761695830382135)
                    ·
                      rfl

theorem cell22_242297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 4].length) (baseStart_242297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242297 prefixEnd_242297 := by exact prefixLift 242297
  have htrace : WordTrace (prefixWord ++ tailWord_242297) baseStart_242297 baseEnd_242297 := by
    simpa [prefixWord, tailWord_242297, baseEnd_242297] using wordTrace_append hprefix tailTrace_242297
  have hstable : (prefixWord ++ tailWord_242297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242297).length < 2 ^ (prefixWord ++ tailWord_242297).sum := by decide
  have hdescent : baseEnd_242297 < baseStart_242297 := by decide
  rcases family_descends (prefixWord ++ tailWord_242297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242314 : List Nat := [3, 1, 2, 3, 3, 1, 3, 1, 1, 4]
def baseStart_242314 : Nat := 118140960795 + 242314 * 2 ^ 59
def prefixEnd_242314 : Nat := 4983230072969 + 3 ^ 40 * 242314 * 2
def baseEnd_242314 : Nat := 82949034209113452707083

theorem tailTrace_242314 : CollatzResearch.WordTrace tailWord_242314 prefixEnd_242314 82949034209113452707083 := by
  unfold tailWord_242314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2209479411036309195391499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5891945096096824521043997 2209479411036309195391499)
  ·
    refine ⟨3314219116554463793087249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2209479411036309195391499 3314219116554463793087249)
    ·
      refine ⟨2485664337415847844815437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3314219116554463793087249 2485664337415847844815437)
      ·
        refine ⟨932124126530942941805789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2485664337415847844815437 932124126530942941805789)
        ·
          refine ⟨349546547449103603177171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 932124126530942941805789 349546547449103603177171)
          ·
            refine ⟨524319821173655404765757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349546547449103603177171 524319821173655404765757)
            ·
              refine ⟨196619932940120776787159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 524319821173655404765757 196619932940120776787159)
              ·
                refine ⟨294929899410181165180739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196619932940120776787159 294929899410181165180739)
                ·
                  refine ⟨442394849115271747771109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294929899410181165180739 442394849115271747771109)
                  ·
                    refine ⟨82949034209113452707083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 442394849115271747771109 82949034209113452707083)
                    ·
                      rfl

theorem cell22_242314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_242314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242314 prefixEnd_242314 := by exact prefixLift 242314
  have htrace : WordTrace (prefixWord ++ tailWord_242314) baseStart_242314 baseEnd_242314 := by
    simpa [prefixWord, tailWord_242314, baseEnd_242314] using wordTrace_append hprefix tailTrace_242314
  have hstable : (prefixWord ++ tailWord_242314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242314).length < 2 ^ (prefixWord ++ tailWord_242314).sum := by decide
  have hdescent : baseEnd_242314 < baseStart_242314 := by decide
  rcases family_descends (prefixWord ++ tailWord_242314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242327 : List Nat := [1, 1, 3, 3, 2, 1, 4, 2, 2, 3]
def baseStart_242327 : Nat := 118140960795 + 242327 * 2 ^ 59
def prefixEnd_242327 : Nat := 4983230072969 + 3 ^ 40 * 242327 * 2
def baseEnd_242327 : Nat := 82953484374785752132043

theorem tailTrace_242327 : CollatzResearch.WordTrace tailWord_242327 prefixEnd_242327 82953484374785752132043 := by
  unfold tailWord_242327
  simp only [CollatzResearch.WordTrace]
  refine ⟨8838391793098140001789235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5892261195398760001192823 8838391793098140001789235)
  ·
    refine ⟨13257587689647210002683853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8838391793098140001789235 13257587689647210002683853)
    ·
      refine ⟨4971595383617703751006445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13257587689647210002683853 4971595383617703751006445)
      ·
        refine ⟨1864348268856638906627417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4971595383617703751006445 1864348268856638906627417)
        ·
          refine ⟨1398261201642479179970563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1864348268856638906627417 1398261201642479179970563)
          ·
            refine ⟨2097391802463718769955845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398261201642479179970563 2097391802463718769955845)
            ·
              refine ⟨393260962961947269366721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2097391802463718769955845 393260962961947269366721)
              ·
                refine ⟨294945722221460452025041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393260962961947269366721 294945722221460452025041)
                ·
                  refine ⟨221209291666095339018781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294945722221460452025041 221209291666095339018781)
                  ·
                    refine ⟨82953484374785752132043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221209291666095339018781 82953484374785752132043)
                    ·
                      rfl

theorem cell22_242327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_242327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242327 prefixEnd_242327 := by exact prefixLift 242327
  have htrace : WordTrace (prefixWord ++ tailWord_242327) baseStart_242327 baseEnd_242327 := by
    simpa [prefixWord, tailWord_242327, baseEnd_242327] using wordTrace_append hprefix tailTrace_242327
  have hstable : (prefixWord ++ tailWord_242327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242327).length < 2 ^ (prefixWord ++ tailWord_242327).sum := by decide
  have hdescent : baseEnd_242327 < baseStart_242327 := by decide
  rcases family_descends (prefixWord ++ tailWord_242327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242355 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 5, 3]
def baseStart_242355 : Nat := 118140960795 + 242355 * 2 ^ 59
def prefixEnd_242355 : Nat := 4983230072969 + 3 ^ 40 * 242355 * 2
def baseEnd_242355 : Nat := 82963069347003012431957

theorem tailTrace_242355 : CollatzResearch.WordTrace tailWord_242355 prefixEnd_242355 82963069347003012431957 := by
  unfold tailWord_242355
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839413036996700783808519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5892942024664467189205679 8839413036996700783808519)
  ·
    refine ⟨13259119555495051175712779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8839413036996700783808519 13259119555495051175712779)
    ·
      refine ⟨19888679333242576763569169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13259119555495051175712779 19888679333242576763569169)
      ·
        refine ⟨14916509499931932572676877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19888679333242576763569169 14916509499931932572676877)
        ·
          refine ⟨5593691062474474714753829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14916509499931932572676877 5593691062474474714753829)
          ·
            refine ⟨1048817074213964009016343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5593691062474474714753829 1048817074213964009016343)
            ·
              refine ⟨1573225611320946013524515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048817074213964009016343 1573225611320946013524515)
              ·
                refine ⟨2359838416981419020286773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573225611320946013524515 2359838416981419020286773)
                ·
                  refine ⟨221234851592008033151885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2359838416981419020286773 221234851592008033151885)
                  ·
                    refine ⟨82963069347003012431957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221234851592008033151885 82963069347003012431957)
                    ·
                      rfl

theorem cell22_242355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 3].length) (baseStart_242355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242355 prefixEnd_242355 := by exact prefixLift 242355
  have htrace : WordTrace (prefixWord ++ tailWord_242355) baseStart_242355 baseEnd_242355 := by
    simpa [prefixWord, tailWord_242355, baseEnd_242355] using wordTrace_append hprefix tailTrace_242355
  have hstable : (prefixWord ++ tailWord_242355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242355).length < 2 ^ (prefixWord ++ tailWord_242355).sum := by decide
  have hdescent : baseEnd_242355 < baseStart_242355 := by decide
  rcases family_descends (prefixWord ++ tailWord_242355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242357 : List Nat := [1, 3, 3, 3, 1, 2, 3, 6]
def baseStart_242357 : Nat := 118140960795 + 242357 * 2 ^ 59
def prefixEnd_242357 : Nat := 4983230072969 + 3 ^ 40 * 242357 * 2
def baseEnd_242357 : Nat := 9218194887541741542439

theorem tailTrace_242357 : CollatzResearch.WordTrace tailWord_242357 prefixEnd_242357 9218194887541741542439 := by
  unfold tailWord_242357
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839485982989455125381325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5892990655326303416920883 8839485982989455125381325)
  ·
    refine ⟨3314807243621045672017997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8839485982989455125381325 3314807243621045672017997)
    ·
      refine ⟨1243052716357892127006749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3314807243621045672017997 1243052716357892127006749)
      ·
        refine ⟨466144768634209547627531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1243052716357892127006749 466144768634209547627531)
        ·
          refine ⟨699217152951314321441297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466144768634209547627531 699217152951314321441297)
          ·
            refine ⟨524412864713485741080973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699217152951314321441297 524412864713485741080973)
            ·
              refine ⟨196654824267557152905365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 524412864713485741080973 196654824267557152905365)
              ·
                refine ⟨9218194887541741542439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196654824267557152905365 9218194887541741542439)
                ·
                  rfl

theorem cell22_242357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 6].length) (baseStart_242357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242357 prefixEnd_242357 := by exact prefixLift 242357
  have htrace : WordTrace (prefixWord ++ tailWord_242357) baseStart_242357 baseEnd_242357 := by
    simpa [prefixWord, tailWord_242357, baseEnd_242357] using wordTrace_append hprefix tailTrace_242357
  have hstable : (prefixWord ++ tailWord_242357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242357).length < 2 ^ (prefixWord ++ tailWord_242357).sum := by decide
  have hdescent : baseEnd_242357 < baseStart_242357 := by decide
  rcases family_descends (prefixWord ++ tailWord_242357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242359 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 2, 4]
def baseStart_242359 : Nat := 118140960795 + 242359 * 2 ^ 59
def prefixEnd_242359 : Nat := 4983230072969 + 3 ^ 40 * 242359 * 2
def baseEnd_242359 : Nat := 82964438628748335331945

theorem tailTrace_242359 : CollatzResearch.WordTrace tailWord_242359 prefixEnd_242359 82964438628748335331945 := by
  unfold tailWord_242359
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839558928982209466954131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5893039285988139644636087 8839558928982209466954131)
  ·
    refine ⟨13259338393473314200431197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8839558928982209466954131 13259338393473314200431197)
    ·
      refine ⟨4972251897552492825161699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13259338393473314200431197 4972251897552492825161699)
      ·
        refine ⟨7458377846328739237742549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4972251897552492825161699 7458377846328739237742549)
        ·
          refine ⟨174805730773329825884591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7458377846328739237742549 174805730773329825884591)
          ·
            refine ⟨262208596159994738826887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174805730773329825884591 262208596159994738826887)
            ·
              refine ⟨393312894239992108240331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262208596159994738826887 393312894239992108240331)
              ·
                refine ⟨589969341359988162360497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393312894239992108240331 589969341359988162360497)
                ·
                  refine ⟨442477006019991121770373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589969341359988162360497 442477006019991121770373)
                  ·
                    refine ⟨82964438628748335331945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 442477006019991121770373 82964438628748335331945)
                    ·
                      rfl

theorem cell22_242359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_242359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242359 prefixEnd_242359 := by exact prefixLift 242359
  have htrace : WordTrace (prefixWord ++ tailWord_242359) baseStart_242359 baseEnd_242359 := by
    simpa [prefixWord, tailWord_242359, baseEnd_242359] using wordTrace_append hprefix tailTrace_242359
  have hstable : (prefixWord ++ tailWord_242359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242359).length < 2 ^ (prefixWord ++ tailWord_242359).sum := by decide
  have hdescent : baseEnd_242359 < baseStart_242359 := by decide
  rcases family_descends (prefixWord ++ tailWord_242359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242374 : List Nat := [6, 1, 2, 1, 2, 1, 9]
def baseStart_242374 : Nat := 118140960795 + 242374 * 2 ^ 59
def prefixEnd_242374 : Nat := 4983230072969 + 3 ^ 40 * 242374 * 2
def baseEnd_242374 : Nat := 3072947164270122081737

theorem tailTrace_242374 : CollatzResearch.WordTrace tailWord_242374 prefixEnd_242374 3072947164270122081737 := by
  unfold tailWord_242374
  simp only [CollatzResearch.WordTrace]
  refine ⟨276253313247745844648443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5893404015951911352500117 276253313247745844648443)
  ·
    refine ⟨414379969871618766972665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276253313247745844648443 414379969871618766972665)
    ·
      refine ⟨310784977403714075229499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414379969871618766972665 310784977403714075229499)
      ·
        refine ⟨466177466105571112844249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310784977403714075229499 466177466105571112844249)
        ·
          refine ⟨349633099579178334633187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466177466105571112844249 349633099579178334633187)
          ·
            refine ⟨524449649368767501949781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349633099579178334633187 524449649368767501949781)
            ·
              refine ⟨3072947164270122081737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 524449649368767501949781 3072947164270122081737)
              ·
                rfl

theorem cell22_242374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 9].length) (baseStart_242374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242374 prefixEnd_242374 := by exact prefixLift 242374
  have htrace : WordTrace (prefixWord ++ tailWord_242374) baseStart_242374 baseEnd_242374 := by
    simpa [prefixWord, tailWord_242374, baseEnd_242374] using wordTrace_append hprefix tailTrace_242374
  have hstable : (prefixWord ++ tailWord_242374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242374).length < 2 ^ (prefixWord ++ tailWord_242374).sum := by decide
  have hdescent : baseEnd_242374 < baseStart_242374 := by decide
  rcases family_descends (prefixWord ++ tailWord_242374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242505 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 2, 6]
def baseStart_242505 : Nat := 118140960795 + 242505 * 2 ^ 59
def prefixEnd_242505 : Nat := 4983230072969 + 3 ^ 40 * 242505 * 2
def baseEnd_242505 : Nat := 83014417412452621181497

theorem tailTrace_242505 : CollatzResearch.WordTrace tailWord_242505 prefixEnd_242505 83014417412452621181497 := by
  unfold tailWord_242505
  simp only [CollatzResearch.WordTrace]
  refine ⟨8844883986453276401768969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5896589324302184267845979 8844883986453276401768969)
  ·
    refine ⟨6633662989839957301326727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8844883986453276401768969 6633662989839957301326727)
    ·
      refine ⟨9950494484759935951990091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6633662989839957301326727 9950494484759935951990091)
      ·
        refine ⟨14925741727139903927985137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9950494484759935951990091 14925741727139903927985137)
        ·
          refine ⟨11194306295354927945988853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14925741727139903927985137 11194306295354927945988853)
          ·
            refine ⟨1049466215189524494936455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11194306295354927945988853 1049466215189524494936455)
            ·
              refine ⟨1574199322784286742404683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049466215189524494936455 1574199322784286742404683)
              ·
                refine ⟨2361298984176430113607025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574199322784286742404683 2361298984176430113607025)
                ·
                  refine ⟨1770974238132322585205269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2361298984176430113607025 1770974238132322585205269)
                  ·
                    refine ⟨83014417412452621181497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1770974238132322585205269 83014417412452621181497)
                    ·
                      rfl

theorem cell22_242505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_242505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242505 prefixEnd_242505 := by exact prefixLift 242505
  have htrace : WordTrace (prefixWord ++ tailWord_242505) baseStart_242505 baseEnd_242505 := by
    simpa [prefixWord, tailWord_242505, baseEnd_242505] using wordTrace_append hprefix tailTrace_242505
  have hstable : (prefixWord ++ tailWord_242505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242505).length < 2 ^ (prefixWord ++ tailWord_242505).sum := by decide
  have hdescent : baseEnd_242505 < baseStart_242505 := by decide
  rcases family_descends (prefixWord ++ tailWord_242505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242524 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 5, 3]
def baseStart_242524 : Nat := 118140960795 + 242524 * 2 ^ 59
def prefixEnd_242524 : Nat := 4983230072969 + 3 ^ 40 * 242524 * 2
def baseEnd_242524 : Nat := 83020921500742904956439

theorem tailTrace_242524 : CollatzResearch.WordTrace tailWord_242524 prefixEnd_242524 83020921500742904956439 := by
  unfold tailWord_242524
  simp only [CollatzResearch.WordTrace]
  refine ⟨4422788486692221323355313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5897051315589628431140417 4422788486692221323355313)
  ·
    refine ⟨3317091365019165992516485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4422788486692221323355313 3317091365019165992516485)
    ·
      refine ⟨621954630941093623596841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3317091365019165992516485 621954630941093623596841)
      ·
        refine ⟨466465973205820217697631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621954630941093623596841 466465973205820217697631)
        ·
          refine ⟨699698959808730326546447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466465973205820217697631 699698959808730326546447)
          ·
            refine ⟨1049548439713095489819671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699698959808730326546447 1049548439713095489819671)
            ·
              refine ⟨1574322659569643234729507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049548439713095489819671 1574322659569643234729507)
              ·
                refine ⟨2361483989354464852094261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574322659569643234729507 2361483989354464852094261)
                ·
                  refine ⟨221389124001981079883837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2361483989354464852094261 221389124001981079883837)
                  ·
                    refine ⟨83020921500742904956439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221389124001981079883837 83020921500742904956439)
                    ·
                      rfl

theorem cell22_242524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_242524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242524 prefixEnd_242524 := by exact prefixLift 242524
  have htrace : WordTrace (prefixWord ++ tailWord_242524) baseStart_242524 baseEnd_242524 := by
    simpa [prefixWord, tailWord_242524, baseEnd_242524] using wordTrace_append hprefix tailTrace_242524
  have hstable : (prefixWord ++ tailWord_242524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242524).length < 2 ^ (prefixWord ++ tailWord_242524).sum := by decide
  have hdescent : baseEnd_242524 < baseStart_242524 := by decide
  rcases family_descends (prefixWord ++ tailWord_242524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242558 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_242558 : Nat := 118140960795 + 242558 * 2 ^ 59
def prefixEnd_242558 : Nat := 4983230072969 + 3 ^ 40 * 242558 * 2
def baseEnd_242558 : Nat := 83032560395578149606335

theorem tailTrace_242558 : CollatzResearch.WordTrace tailWord_242558 prefixEnd_242558 83032560395578149606335 := by
  unfold tailWord_242558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105852131907658306681041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5897878036840844302298885 1105852131907658306681041)
  ·
    refine ⟨829389098930743730010781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1105852131907658306681041 829389098930743730010781)
    ·
      refine ⟨311020912099028898754043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 829389098930743730010781 311020912099028898754043)
      ·
        refine ⟨466531368148543348131065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311020912099028898754043 466531368148543348131065)
        ·
          refine ⟨349898526111407511098299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466531368148543348131065 349898526111407511098299)
          ·
            refine ⟨524847789167111266647449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349898526111407511098299 524847789167111266647449)
            ·
              refine ⟨393635841875333449985587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524847789167111266647449 393635841875333449985587)
              ·
                refine ⟨590453762813000174978381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393635841875333449985587 590453762813000174978381)
                ·
                  refine ⟨221420161054875065616893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590453762813000174978381 221420161054875065616893)
                  ·
                    refine ⟨83032560395578149606335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221420161054875065616893 83032560395578149606335)
                    ·
                      rfl

theorem cell22_242558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_242558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242558 prefixEnd_242558 := by exact prefixLift 242558
  have htrace : WordTrace (prefixWord ++ tailWord_242558) baseStart_242558 baseEnd_242558 := by
    simpa [prefixWord, tailWord_242558, baseEnd_242558] using wordTrace_append hprefix tailTrace_242558
  have hstable : (prefixWord ++ tailWord_242558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242558).length < 2 ^ (prefixWord ++ tailWord_242558).sum := by decide
  have hdescent : baseEnd_242558 < baseStart_242558 := by decide
  rcases family_descends (prefixWord ++ tailWord_242558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242616 : List Nat := [2, 1, 2, 1, 2, 5, 3, 2, 4]
def baseStart_242616 : Nat := 118140960795 + 242616 * 2 ^ 59
def prefixEnd_242616 : Nat := 4983230072969 + 3 ^ 40 * 242616 * 2
def baseEnd_242616 : Nat := 27684138326961777218719

theorem tailTrace_242616 : CollatzResearch.WordTrace tailWord_242616 prefixEnd_242616 27684138326961777218719 := by
  unfold tailWord_242616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424466244525571179529851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5899288326034094906039801 4424466244525571179529851)
  ·
    refine ⟨6636699366788356769294777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4424466244525571179529851 6636699366788356769294777)
    ·
      refine ⟨4977524525091267576971083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6636699366788356769294777 4977524525091267576971083)
      ·
        refine ⟨7466286787636901365456625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977524525091267576971083 7466286787636901365456625)
        ·
          refine ⟨5599715090727676024092469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7466286787636901365456625 5599715090727676024092469)
          ·
            refine ⟨524973289755719627258669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5599715090727676024092469 524973289755719627258669)
            ·
              refine ⟨196864983658394860222001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 524973289755719627258669 196864983658394860222001)
              ·
                refine ⟨147648737743796145166501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196864983658394860222001 147648737743796145166501)
                ·
                  refine ⟨27684138326961777218719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147648737743796145166501 27684138326961777218719)
                  ·
                    rfl

theorem cell22_242616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 4].length) (baseStart_242616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242616 prefixEnd_242616 := by exact prefixLift 242616
  have htrace : WordTrace (prefixWord ++ tailWord_242616) baseStart_242616 baseEnd_242616 := by
    simpa [prefixWord, tailWord_242616, baseEnd_242616] using wordTrace_append hprefix tailTrace_242616
  have hstable : (prefixWord ++ tailWord_242616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242616).length < 2 ^ (prefixWord ++ tailWord_242616).sum := by decide
  have hdescent : baseEnd_242616 < baseStart_242616 := by decide
  rcases family_descends (prefixWord ++ tailWord_242616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242631 : List Nat := [1, 1, 4, 1, 1, 2, 6, 1, 2, 3]
def baseStart_242631 : Nat := 118140960795 + 242631 * 2 ^ 59
def prefixEnd_242631 : Nat := 4983230072969 + 3 ^ 40 * 242631 * 2
def baseEnd_242631 : Nat := 83057549787430292531111

theorem tailTrace_242631 : CollatzResearch.WordTrace tailWord_242631 prefixEnd_242631 83057549787430292531111 := by
  unfold tailWord_242631
  simp only [CollatzResearch.WordTrace]
  refine ⟨8849479583996799920855747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5899653055997866613903831 8849479583996799920855747)
  ·
    refine ⟨13274219375995199881283621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8849479583996799920855747 13274219375995199881283621)
    ·
      refine ⟨2488916132999099977740679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13274219375995199881283621 2488916132999099977740679)
      ·
        refine ⟨3733374199498649966611019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488916132999099977740679 3733374199498649966611019)
        ·
          refine ⟨5600061299247974949916529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733374199498649966611019 5600061299247974949916529)
          ·
            refine ⟨4200045974435981212437397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5600061299247974949916529 4200045974435981212437397)
            ·
              refine ⟨196877155051686619333003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4200045974435981212437397 196877155051686619333003)
              ·
                refine ⟨295315732577529928999505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196877155051686619333003 295315732577529928999505)
                ·
                  refine ⟨221486799433147446749629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295315732577529928999505 221486799433147446749629)
                  ·
                    refine ⟨83057549787430292531111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221486799433147446749629 83057549787430292531111)
                    ·
                      rfl

theorem cell22_242631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_242631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242631 prefixEnd_242631 := by exact prefixLift 242631
  have htrace : WordTrace (prefixWord ++ tailWord_242631) baseStart_242631 baseEnd_242631 := by
    simpa [prefixWord, tailWord_242631, baseEnd_242631] using wordTrace_append hprefix tailTrace_242631
  have hstable : (prefixWord ++ tailWord_242631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242631).length < 2 ^ (prefixWord ++ tailWord_242631).sum := by decide
  have hdescent : baseEnd_242631 < baseStart_242631 := by decide
  rcases family_descends (prefixWord ++ tailWord_242631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242646 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_242646 : Nat := 118140960795 + 242646 * 2 ^ 59
def prefixEnd_242646 : Nat := 4983230072969 + 3 ^ 40 * 242646 * 2
def baseEnd_242646 : Nat := 83062684593975253406065

theorem tailTrace_242646 : CollatzResearch.WordTrace tailWord_242646 prefixEnd_242646 83062684593975253406065 := by
  unfold tailWord_242646
  simp only [CollatzResearch.WordTrace]
  refine ⟨553126667433903592665737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5900017785961638321767861 553126667433903592665737)
  ·
    refine ⟨414845000575427694499303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 553126667433903592665737 414845000575427694499303)
    ·
      refine ⟨622267500863141541748955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414845000575427694499303 622267500863141541748955)
      ·
        refine ⟨933401251294712312623433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622267500863141541748955 933401251294712312623433)
        ·
          refine ⟨700050938471034234467575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 933401251294712312623433 700050938471034234467575)
          ·
            refine ⟨1050076407706551351701363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700050938471034234467575 1050076407706551351701363)
            ·
              refine ⟨1575114611559827027552045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050076407706551351701363 1575114611559827027552045)
              ·
                refine ⟨590667979334935135332017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1575114611559827027552045 590667979334935135332017)
                ·
                  refine ⟨443000984501201351499013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590667979334935135332017 443000984501201351499013)
                  ·
                    refine ⟨83062684593975253406065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 443000984501201351499013 83062684593975253406065)
                    ·
                      rfl

theorem cell22_242646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_242646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242646 prefixEnd_242646 := by exact prefixLift 242646
  have htrace : WordTrace (prefixWord ++ tailWord_242646) baseStart_242646 baseEnd_242646 := by
    simpa [prefixWord, tailWord_242646, baseEnd_242646] using wordTrace_append hprefix tailTrace_242646
  have hstable : (prefixWord ++ tailWord_242646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242646).length < 2 ^ (prefixWord ++ tailWord_242646).sum := by decide
  have hdescent : baseEnd_242646 < baseStart_242646 := by decide
  rcases family_descends (prefixWord ++ tailWord_242646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242689 : List Nat := [1, 2, 4, 1, 2, 2, 2, 3, 5]
def baseStart_242689 : Nat := 118140960795 + 242689 * 2 ^ 59
def prefixEnd_242689 : Nat := 4983230072969 + 3 ^ 40 * 242689 * 2
def baseEnd_242689 : Nat := 27692468124245824860311

theorem tailTrace_242689 : CollatzResearch.WordTrace tailWord_242689 prefixEnd_242689 27692468124245824860311 := by
  unfold tailWord_242689
  simp only [CollatzResearch.WordTrace]
  refine ⟨8851595017786675826467121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5901063345191117217644747 8851595017786675826467121)
  ·
    refine ⟨6638696263340006869850341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8851595017786675826467121 6638696263340006869850341)
    ·
      refine ⟨1244755549376251288096939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6638696263340006869850341 1244755549376251288096939)
      ·
        refine ⟨1867133324064376932145409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244755549376251288096939 1867133324064376932145409)
        ·
          refine ⟨1400349993048282699109057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1867133324064376932145409 1400349993048282699109057)
          ·
            refine ⟨1050262494786212024331793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400349993048282699109057 1050262494786212024331793)
            ·
              refine ⟨787696871089659018248845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050262494786212024331793 787696871089659018248845)
              ·
                refine ⟨295386326658622131843317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 787696871089659018248845 295386326658622131843317)
                ·
                  refine ⟨27692468124245824860311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 295386326658622131843317 27692468124245824860311)
                  ·
                    rfl

theorem cell22_242689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 5].length) (baseStart_242689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242689 prefixEnd_242689 := by exact prefixLift 242689
  have htrace : WordTrace (prefixWord ++ tailWord_242689) baseStart_242689 baseEnd_242689 := by
    simpa [prefixWord, tailWord_242689, baseEnd_242689] using wordTrace_append hprefix tailTrace_242689
  have hstable : (prefixWord ++ tailWord_242689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242689).length < 2 ^ (prefixWord ++ tailWord_242689).sum := by decide
  have hdescent : baseEnd_242689 < baseStart_242689 := by decide
  rcases family_descends (prefixWord ++ tailWord_242689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242753 : List Nat := [1, 2, 5, 1, 3, 1, 2, 2, 1, 4]
def baseStart_242753 : Nat := 118140960795 + 242753 * 2 ^ 59
def prefixEnd_242753 : Nat := 4983230072969 + 3 ^ 40 * 242753 * 2
def baseEnd_242753 : Nat := 83099312880662640980737

theorem tailTrace_242753 : CollatzResearch.WordTrace tailWord_242753 prefixEnd_242753 83099312880662640980737 := by
  unfold tailWord_242753
  simp only [CollatzResearch.WordTrace]
  refine ⟨8853929289554814756796913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5902619526369876504531275 8853929289554814756796913)
  ·
    refine ⟨6640446967166111067597685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8853929289554814756796913 6640446967166111067597685)
    ·
      refine ⟨622541903171822912587283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6640446967166111067597685 622541903171822912587283)
      ·
        refine ⟨933812854757734368880925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622541903171822912587283 933812854757734368880925)
        ·
          refine ⟨350179820534150388330347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 933812854757734368880925 350179820534150388330347)
          ·
            refine ⟨525269730801225582495521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350179820534150388330347 525269730801225582495521)
            ·
              refine ⟨393952298100919186871641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525269730801225582495521 393952298100919186871641)
              ·
                refine ⟨295464223575689390153731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393952298100919186871641 295464223575689390153731)
                ·
                  refine ⟨443196335363534085230597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295464223575689390153731 443196335363534085230597)
                  ·
                    refine ⟨83099312880662640980737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 443196335363534085230597 83099312880662640980737)
                    ·
                      rfl

theorem cell22_242753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_242753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242753 prefixEnd_242753 := by exact prefixLift 242753
  have htrace : WordTrace (prefixWord ++ tailWord_242753) baseStart_242753 baseEnd_242753 := by
    simpa [prefixWord, tailWord_242753, baseEnd_242753] using wordTrace_append hprefix tailTrace_242753
  have hstable : (prefixWord ++ tailWord_242753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242753).length < 2 ^ (prefixWord ++ tailWord_242753).sum := by decide
  have hdescent : baseEnd_242753 < baseStart_242753 := by decide
  rcases family_descends (prefixWord ++ tailWord_242753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242764 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_242764 : Nat := 118140960795 + 242764 * 2 ^ 59
def prefixEnd_242764 : Nat := 4983230072969 + 3 ^ 40 * 242764 * 2
def baseEnd_242764 : Nat := 83103078405462278955703

theorem tailTrace_242764 : CollatzResearch.WordTrace tailWord_242764 prefixEnd_242764 83103078405462278955703 := by
  unfold tailWord_242764
  simp only [CollatzResearch.WordTrace]
  refine ⟨4427165246257481817723673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5902886995009975756964897 4427165246257481817723673)
  ·
    refine ⟨3320373934693111363292755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4427165246257481817723673 3320373934693111363292755)
    ·
      refine ⟨4980560902039667044939133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3320373934693111363292755 4980560902039667044939133)
      ·
        refine ⟨1867710338264875141852175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4980560902039667044939133 1867710338264875141852175)
        ·
          refine ⟨2801565507397312712778263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867710338264875141852175 2801565507397312712778263)
          ·
            refine ⟨4202348261095969069167395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801565507397312712778263 4202348261095969069167395)
            ·
              refine ⟨6303522391643953603751093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4202348261095969069167395 6303522391643953603751093)
              ·
                refine ⟨590955224216620650351665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6303522391643953603751093 590955224216620650351665)
                ·
                  refine ⟨443216418162465487763749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590955224216620650351665 443216418162465487763749)
                  ·
                    refine ⟨83103078405462278955703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 443216418162465487763749 83103078405462278955703)
                    ·
                      rfl

theorem cell22_242764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_242764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242764 prefixEnd_242764 := by exact prefixLift 242764
  have htrace : WordTrace (prefixWord ++ tailWord_242764) baseStart_242764 baseEnd_242764 := by
    simpa [prefixWord, tailWord_242764, baseEnd_242764] using wordTrace_append hprefix tailTrace_242764
  have hstable : (prefixWord ++ tailWord_242764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242764).length < 2 ^ (prefixWord ++ tailWord_242764).sum := by decide
  have hdescent : baseEnd_242764 < baseStart_242764 := by decide
  rcases family_descends (prefixWord ++ tailWord_242764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242858 : List Nat := [3, 1, 5, 1, 1, 1, 2, 3, 5]
def baseStart_242858 : Nat := 118140960795 + 242858 * 2 ^ 59
def prefixEnd_242858 : Nat := 4983230072969 + 3 ^ 40 * 242858 * 2
def baseEnd_242858 : Nat := 27711752175492455701805

theorem tailTrace_242858 : CollatzResearch.WordTrace tailWord_242858 prefixEnd_242858 27711752175492455701805 := by
  unfold tailWord_242858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214439738543604422342307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5905172636116278459579485 2214439738543604422342307)
  ·
    refine ⟨3321659607815406633513461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2214439738543604422342307 3321659607815406633513461)
    ·
      refine ⟨311405588232694371891887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3321659607815406633513461 311405588232694371891887)
      ·
        refine ⟨467108382349041557837831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311405588232694371891887 467108382349041557837831)
        ·
          refine ⟨700662573523562336756747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467108382349041557837831 700662573523562336756747)
          ·
            refine ⟨1050993860285343505135121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700662573523562336756747 1050993860285343505135121)
            ·
              refine ⟨788245395214007628851341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050993860285343505135121 788245395214007628851341)
              ·
                refine ⟨295592023205252860819253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 788245395214007628851341 295592023205252860819253)
                ·
                  refine ⟨27711752175492455701805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 295592023205252860819253 27711752175492455701805)
                  ·
                    rfl

theorem cell22_242858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_242858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242858 prefixEnd_242858 := by exact prefixLift 242858
  have htrace : WordTrace (prefixWord ++ tailWord_242858) baseStart_242858 baseEnd_242858 := by
    simpa [prefixWord, tailWord_242858, baseEnd_242858] using wordTrace_append hprefix tailTrace_242858
  have hstable : (prefixWord ++ tailWord_242858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242858).length < 2 ^ (prefixWord ++ tailWord_242858).sum := by decide
  have hdescent : baseEnd_242858 < baseStart_242858 := by decide
  rcases family_descends (prefixWord ++ tailWord_242858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242871 : List Nat := [1, 1, 3, 1, 4, 1, 2, 4, 1, 4]
def baseStart_242871 : Nat := 118140960795 + 242871 * 2 ^ 59
def prefixEnd_242871 : Nat := 4983230072969 + 3 ^ 40 * 242871 * 2
def baseEnd_242871 : Nat := 83139706692149666530375

theorem tailTrace_242871 : CollatzResearch.WordTrace tailWord_242871 prefixEnd_242871 83139706692149666530375 := by
  unfold tailWord_242871
  simp only [CollatzResearch.WordTrace]
  refine ⟨8858233103127320909592467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5905488735418213939728311 8858233103127320909592467)
  ·
    refine ⟨13287349654690981364388701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8858233103127320909592467 13287349654690981364388701)
    ·
      refine ⟨4982756120509118011645763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13287349654690981364388701 4982756120509118011645763)
      ·
        refine ⟨7474134180763677017468645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4982756120509118011645763 7474134180763677017468645)
        ·
          refine ⟨1401400158893189440775371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7474134180763677017468645 1401400158893189440775371)
          ·
            refine ⟨2102100238339784161163057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401400158893189440775371 2102100238339784161163057)
            ·
              refine ⟨1576575178754838120872293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102100238339784161163057 1576575178754838120872293)
              ·
                refine ⟨295607846016532147663555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1576575178754838120872293 295607846016532147663555)
                ·
                  refine ⟨443411769024798221495333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295607846016532147663555 443411769024798221495333)
                  ·
                    refine ⟨83139706692149666530375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 443411769024798221495333 83139706692149666530375)
                    ·
                      rfl

theorem cell22_242871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_242871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242871 prefixEnd_242871 := by exact prefixLift 242871
  have htrace : WordTrace (prefixWord ++ tailWord_242871) baseStart_242871 baseEnd_242871 := by
    simpa [prefixWord, tailWord_242871, baseEnd_242871] using wordTrace_append hprefix tailTrace_242871
  have hstable : (prefixWord ++ tailWord_242871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242871).length < 2 ^ (prefixWord ++ tailWord_242871).sum := by decide
  have hdescent : baseEnd_242871 < baseStart_242871 := by decide
  rcases family_descends (prefixWord ++ tailWord_242871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242888 : List Nat := [2, 1, 3, 1, 2, 1, 6, 1, 1, 4]
def baseStart_242888 : Nat := 118140960795 + 242888 * 2 ^ 59
def prefixEnd_242888 : Nat := 4983230072969 + 3 ^ 40 * 242888 * 2
def baseEnd_242888 : Nat := 83145526139567288855323

theorem tailTrace_242888 : CollatzResearch.WordTrace tailWord_242888 prefixEnd_242888 83145526139567288855323 := by
  unfold tailWord_242888
  simp only [CollatzResearch.WordTrace]
  refine ⟨4429426572032866406480659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5905902096043821875307545 4429426572032866406480659)
  ·
    refine ⟨6644139858049299609720989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4429426572032866406480659 6644139858049299609720989)
    ·
      refine ⟨2491552446768487353645371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6644139858049299609720989 2491552446768487353645371)
      ·
        refine ⟨3737328670152731030468057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2491552446768487353645371 3737328670152731030468057)
        ·
          refine ⟨2802996502614548272851043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3737328670152731030468057 2802996502614548272851043)
          ·
            refine ⟨4204494753921822409276565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802996502614548272851043 4204494753921822409276565)
            ·
              refine ⟨197085691590085425434839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4204494753921822409276565 197085691590085425434839)
              ·
                refine ⟨295628537385128138152259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197085691590085425434839 295628537385128138152259)
                ·
                  refine ⟨443442806077692207228389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295628537385128138152259 443442806077692207228389)
                  ·
                    refine ⟨83145526139567288855323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 443442806077692207228389 83145526139567288855323)
                    ·
                      rfl

theorem cell22_242888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_242888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242888 prefixEnd_242888 := by exact prefixLift 242888
  have htrace : WordTrace (prefixWord ++ tailWord_242888) baseStart_242888 baseEnd_242888 := by
    simpa [prefixWord, tailWord_242888, baseEnd_242888] using wordTrace_append hprefix tailTrace_242888
  have hstable : (prefixWord ++ tailWord_242888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242888).length < 2 ^ (prefixWord ++ tailWord_242888).sum := by decide
  have hdescent : baseEnd_242888 < baseStart_242888 := by decide
  rcases family_descends (prefixWord ++ tailWord_242888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242929 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 1, 9]
def baseStart_242929 : Nat := 118140960795 + 242929 * 2 ^ 59
def prefixEnd_242929 : Nat := 4983230072969 + 3 ^ 40 * 242929 * 2
def baseEnd_242929 : Nat := 83159561277456848580197

theorem tailTrace_242929 : CollatzResearch.WordTrace tailWord_242929 prefixEnd_242929 83159561277456848580197 := by
  unfold tailWord_242929
  simp only [CollatzResearch.WordTrace]
  refine ⟨8860348536917196815203841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5906899024611464543469227 8860348536917196815203841)
  ·
    refine ⟨6645261402687897611402881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8860348536917196815203841 6645261402687897611402881)
    ·
      refine ⟨4983946052015923208552161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6645261402687897611402881 4983946052015923208552161)
      ·
        refine ⟨3737959539011942406414121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4983946052015923208552161 3737959539011942406414121)
        ·
          refine ⟨2803469654258956804810591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3737959539011942406414121 2803469654258956804810591)
          ·
            refine ⟨4205204481388435207215887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803469654258956804810591 4205204481388435207215887)
            ·
              refine ⟨6307806722082652810823831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4205204481388435207215887 6307806722082652810823831)
              ·
                refine ⟨9461710083123979216235747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6307806722082652810823831 9461710083123979216235747)
                ·
                  refine ⟨14192565124685968824353621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9461710083123979216235747 14192565124685968824353621)
                  ·
                    refine ⟨83159561277456848580197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 14192565124685968824353621 83159561277456848580197)
                    ·
                      rfl

theorem cell22_242929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_242929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242929 prefixEnd_242929 := by exact prefixLift 242929
  have htrace : WordTrace (prefixWord ++ tailWord_242929) baseStart_242929 baseEnd_242929 := by
    simpa [prefixWord, tailWord_242929, baseEnd_242929] using wordTrace_append hprefix tailTrace_242929
  have hstable : (prefixWord ++ tailWord_242929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242929).length < 2 ^ (prefixWord ++ tailWord_242929).sum := by decide
  have hdescent : baseEnd_242929 < baseStart_242929 := by decide
  rcases family_descends (prefixWord ++ tailWord_242929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242931 : List Nat := [1, 1, 1, 2, 2, 5, 4, 6]
def baseStart_242931 : Nat := 118140960795 + 242931 * 2 ^ 59
def prefixEnd_242931 : Nat := 4983230072969 + 3 ^ 40 * 242931 * 2
def baseEnd_242931 : Nat := 9240027324258834447799

theorem tailTrace_242931 : CollatzResearch.WordTrace tailWord_242931 prefixEnd_242931 9240027324258834447799 := by
  unfold tailWord_242931
  simp only [CollatzResearch.WordTrace]
  refine ⟨8860421482909951156776647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5906947655273300771184431 8860421482909951156776647)
  ·
    refine ⟨13290632224364926735164971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8860421482909951156776647 13290632224364926735164971)
    ·
      refine ⟨19935948336547390102747457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13290632224364926735164971 19935948336547390102747457)
      ·
        refine ⟨14951961252410542577060593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19935948336547390102747457 14951961252410542577060593)
        ·
          refine ⟨11213970939307906932795445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14951961252410542577060593 11213970939307906932795445)
          ·
            refine ⟨1051309775560116274949573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11213970939307906932795445 1051309775560116274949573)
            ·
              refine ⟨197120582917521801553045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1051309775560116274949573 197120582917521801553045)
              ·
                refine ⟨9240027324258834447799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197120582917521801553045 9240027324258834447799)
                ·
                  rfl

theorem cell22_242931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 6].length) (baseStart_242931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242931 prefixEnd_242931 := by exact prefixLift 242931
  have htrace : WordTrace (prefixWord ++ tailWord_242931) baseStart_242931 baseEnd_242931 := by
    simpa [prefixWord, tailWord_242931, baseEnd_242931] using wordTrace_append hprefix tailTrace_242931
  have hstable : (prefixWord ++ tailWord_242931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242931).length < 2 ^ (prefixWord ++ tailWord_242931).sum := by decide
  have hdescent : baseEnd_242931 < baseStart_242931 := by decide
  rcases family_descends (prefixWord ++ tailWord_242931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242944 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 1, 8]
def baseStart_242944 : Nat := 118140960795 + 242944 * 2 ^ 59
def prefixEnd_242944 : Nat := 4983230072969 + 3 ^ 40 * 242944 * 2
def baseEnd_242944 : Nat := 83164696084001809455151

theorem tailTrace_242944 : CollatzResearch.WordTrace tailWord_242944 prefixEnd_242944 83164696084001809455151 := by
  unfold tailWord_242944
  simp only [CollatzResearch.WordTrace]
  refine ⟨4430447815931427188499943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5907263754575236251333257 4430447815931427188499943)
  ·
    refine ⟨6645671723897140782749915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4430447815931427188499943 6645671723897140782749915)
    ·
      refine ⟨9968507585845711174124873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6645671723897140782749915 9968507585845711174124873)
      ·
        refine ⟨7476380689384283380593655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9968507585845711174124873 7476380689384283380593655)
        ·
          refine ⟨11214571034076425070890483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7476380689384283380593655 11214571034076425070890483)
          ·
            refine ⟨16821856551114637606335725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11214571034076425070890483 16821856551114637606335725)
            ·
              refine ⟨6308196206667989102375897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16821856551114637606335725 6308196206667989102375897)
              ·
                refine ⟨4731147155000991826781923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6308196206667989102375897 4731147155000991826781923)
                ·
                  refine ⟨7096720732501487740172885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731147155000991826781923 7096720732501487740172885)
                  ·
                    refine ⟨83164696084001809455151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7096720732501487740172885 83164696084001809455151)
                    ·
                      rfl

theorem cell22_242944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_242944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_242944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_242944 prefixEnd_242944 := by exact prefixLift 242944
  have htrace : WordTrace (prefixWord ++ tailWord_242944) baseStart_242944 baseEnd_242944 := by
    simpa [prefixWord, tailWord_242944, baseEnd_242944] using wordTrace_append hprefix tailTrace_242944
  have hstable : (prefixWord ++ tailWord_242944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242944).length < 2 ^ (prefixWord ++ tailWord_242944).sum := by decide
  have hdescent : baseEnd_242944 < baseStart_242944 := by decide
  rcases family_descends (prefixWord ++ tailWord_242944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243053 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_243053 : Nat := 118140960795 + 243053 * 2 ^ 59
def prefixEnd_243053 : Nat := 4983230072969 + 3 ^ 40 * 243053 * 2
def baseEnd_243053 : Nat := 83202009011561858479817

theorem tailTrace_243053 : CollatzResearch.WordTrace tailWord_243053 prefixEnd_243053 83202009011561858479817 := by
  unfold tailWord_243053
  simp only [CollatzResearch.WordTrace]
  refine ⟨8864871188467965992717813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5909914125645310661811875 8864871188467965992717813)
  ·
    refine ⟨831081673918871811817295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8864871188467965992717813 831081673918871811817295)
    ·
      refine ⟨1246622510878307717725943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 831081673918871811817295 1246622510878307717725943)
      ·
        refine ⟨1869933766317461576588915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246622510878307717725943 1869933766317461576588915)
        ·
          refine ⟨2804900649476192364883373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869933766317461576588915 2804900649476192364883373)
          ·
            refine ⟨1051837743553572136831265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2804900649476192364883373 1051837743553572136831265)
            ·
              refine ⟨788878307665179102623449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051837743553572136831265 788878307665179102623449)
              ·
                refine ⟨591658730748884326967587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788878307665179102623449 591658730748884326967587)
                ·
                  refine ⟨887488096123326490451381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591658730748884326967587 887488096123326490451381)
                  ·
                    refine ⟨83202009011561858479817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 887488096123326490451381 83202009011561858479817)
                    ·
                      rfl

theorem cell22_243053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_243053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243053 prefixEnd_243053 := by exact prefixLift 243053
  have htrace : WordTrace (prefixWord ++ tailWord_243053) baseStart_243053 baseEnd_243053 := by
    simpa [prefixWord, tailWord_243053, baseEnd_243053] using wordTrace_append hprefix tailTrace_243053
  have hstable : (prefixWord ++ tailWord_243053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243053).length < 2 ^ (prefixWord ++ tailWord_243053).sum := by decide
  have hdescent : baseEnd_243053 < baseStart_243053 := by decide
  rcases family_descends (prefixWord ++ tailWord_243053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243100 : List Nat := [2, 2, 3, 4, 1, 1, 1, 8]
def baseStart_243100 : Nat := 118140960795 + 243100 * 2 ^ 59
def prefixEnd_243100 : Nat := 4983230072969 + 3 ^ 40 * 243100 * 2
def baseEnd_243100 : Nat := 9246455341341044728297

theorem tailTrace_243100 : CollatzResearch.WordTrace tailWord_243100 prefixEnd_243100 9246455341341044728297 := by
  unfold tailWord_243100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4433292709648846509839377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5911056946198462013119169 4433292709648846509839377)
  ·
    refine ⟨3324969532236634882379533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4433292709648846509839377 3324969532236634882379533)
    ·
      refine ⟨1246863574588738080892325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3324969532236634882379533 1246863574588738080892325)
      ·
        refine ⟨233786920235388390167311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1246863574588738080892325 233786920235388390167311)
        ·
          refine ⟨350680380353082585250967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233786920235388390167311 350680380353082585250967)
          ·
            refine ⟨526020570529623877876451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350680380353082585250967 526020570529623877876451)
            ·
              refine ⟨789030855794435816814677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526020570529623877876451 789030855794435816814677)
              ·
                refine ⟨9246455341341044728297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 789030855794435816814677 9246455341341044728297)
                ·
                  rfl

theorem cell22_243100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 8].length) (baseStart_243100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243100 prefixEnd_243100 := by exact prefixLift 243100
  have htrace : WordTrace (prefixWord ++ tailWord_243100) baseStart_243100 baseEnd_243100 := by
    simpa [prefixWord, tailWord_243100, baseEnd_243100] using wordTrace_append hprefix tailTrace_243100
  have hstable : (prefixWord ++ tailWord_243100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243100).length < 2 ^ (prefixWord ++ tailWord_243100).sum := by decide
  have hdescent : baseEnd_243100 < baseStart_243100 := by decide
  rcases family_descends (prefixWord ++ tailWord_243100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243138 : List Nat := [3, 5, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_243138 : Nat := 118140960795 + 243138 * 2 ^ 59
def prefixEnd_243138 : Nat := 4983230072969 + 3 ^ 40 * 243138 * 2
def baseEnd_243138 : Nat := 83231106248649970104557

theorem tailTrace_243138 : CollatzResearch.WordTrace tailWord_243138 prefixEnd_243138 83231106248649970104557 := by
  unfold tailWord_243138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2216992848290006377390517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5911980928773350339708045 2216992848290006377390517)
  ·
    refine ⟨207843079527188097880361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2216992848290006377390517 207843079527188097880361)
    ·
      refine ⟨155882309645391073410271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207843079527188097880361 155882309645391073410271)
      ·
        refine ⟨233823464468086610115407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155882309645391073410271 233823464468086610115407)
        ·
          refine ⟨350735196702129915173111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233823464468086610115407 350735196702129915173111)
          ·
            refine ⟨526102795053194872759667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350735196702129915173111 526102795053194872759667)
            ·
              refine ⟨789154192579792309139501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526102795053194872759667 789154192579792309139501)
              ·
                refine ⟨295932822217422115927313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 789154192579792309139501 295932822217422115927313)
                ·
                  refine ⟨221949616663066586945485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295932822217422115927313 221949616663066586945485)
                  ·
                    refine ⟨83231106248649970104557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221949616663066586945485 83231106248649970104557)
                    ·
                      rfl

theorem cell22_243138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_243138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243138 prefixEnd_243138 := by exact prefixLift 243138
  have htrace : WordTrace (prefixWord ++ tailWord_243138) baseStart_243138 baseEnd_243138 := by
    simpa [prefixWord, tailWord_243138, baseEnd_243138] using wordTrace_append hprefix tailTrace_243138
  have hstable : (prefixWord ++ tailWord_243138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243138).length < 2 ^ (prefixWord ++ tailWord_243138).sum := by decide
  have hdescent : baseEnd_243138 < baseStart_243138 := by decide
  rcases family_descends (prefixWord ++ tailWord_243138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243286 : List Nat := [5, 2, 2, 2, 2, 1, 8]
def baseStart_243286 : Nat := 118140960795 + 243286 * 2 ^ 59
def prefixEnd_243286 : Nat := 4983230072969 + 3 ^ 40 * 243286 * 2
def baseEnd_243286 : Nat := 3084509987897293237189

theorem tailTrace_243286 : CollatzResearch.WordTrace tailWord_243286 prefixEnd_243286 3084509987897293237189 := by
  unfold tailWord_243286
  simp only [CollatzResearch.WordTrace]
  refine ⟨554585587288990424121857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5915579597749231190633141 554585587288990424121857)
  ·
    refine ⟨415939190466742818091393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 554585587288990424121857 415939190466742818091393)
    ·
      refine ⟨311954392850057113568545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415939190466742818091393 311954392850057113568545)
      ·
        refine ⟨233965794637542835176409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311954392850057113568545 233965794637542835176409)
        ·
          refine ⟨175474345978157126382307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233965794637542835176409 175474345978157126382307)
          ·
            refine ⟨263211518967235689573461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175474345978157126382307 263211518967235689573461)
            ·
              refine ⟨3084509987897293237189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 263211518967235689573461 3084509987897293237189)
              ·
                rfl

theorem cell22_243286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 8].length) (baseStart_243286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243286 prefixEnd_243286 := by exact prefixLift 243286
  have htrace : WordTrace (prefixWord ++ tailWord_243286) baseStart_243286 baseEnd_243286 := by
    simpa [prefixWord, tailWord_243286, baseEnd_243286] using wordTrace_append hprefix tailTrace_243286
  have hstable : (prefixWord ++ tailWord_243286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243286).length < 2 ^ (prefixWord ++ tailWord_243286).sum := by decide
  have hdescent : baseEnd_243286 < baseStart_243286 := by decide
  rcases family_descends (prefixWord ++ tailWord_243286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243301 : List Nat := [1, 3, 1, 3, 3, 2, 3, 2, 1, 3]
def baseStart_243301 : Nat := 118140960795 + 243301 * 2 ^ 59
def prefixEnd_243301 : Nat := 4983230072969 + 3 ^ 40 * 243301 * 2
def baseEnd_243301 : Nat := 83286904479771878279057

theorem tailTrace_243301 : CollatzResearch.WordTrace tailWord_243301 prefixEnd_243301 83286904479771878279057 := by
  unfold tailWord_243301
  simp only [CollatzResearch.WordTrace]
  refine ⟨8873916491569504347745757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5915944327713002898497171 8873916491569504347745757)
  ·
    refine ⟨3327718684338564130404659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8873916491569504347745757 3327718684338564130404659)
    ·
      refine ⟨4991578026507846195606989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3327718684338564130404659 4991578026507846195606989)
      ·
        refine ⟨1871841759940442323352621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4991578026507846195606989 1871841759940442323352621)
        ·
          refine ⟨701940659977665871257233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1871841759940442323352621 701940659977665871257233)
          ·
            refine ⟨526455494983249403442925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701940659977665871257233 526455494983249403442925)
            ·
              refine ⟨197420810618718526291097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 526455494983249403442925 197420810618718526291097)
              ·
                refine ⟨148065607964038894718323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197420810618718526291097 148065607964038894718323)
                ·
                  refine ⟨222098411946058342077485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148065607964038894718323 222098411946058342077485)
                  ·
                    refine ⟨83286904479771878279057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 222098411946058342077485 83286904479771878279057)
                    ·
                      rfl

theorem cell22_243301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_243301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243301 prefixEnd_243301 := by exact prefixLift 243301
  have htrace : WordTrace (prefixWord ++ tailWord_243301) baseStart_243301 baseEnd_243301 := by
    simpa [prefixWord, tailWord_243301, baseEnd_243301] using wordTrace_append hprefix tailTrace_243301
  have hstable : (prefixWord ++ tailWord_243301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243301).length < 2 ^ (prefixWord ++ tailWord_243301).sum := by decide
  have hdescent : baseEnd_243301 < baseStart_243301 := by decide
  rcases family_descends (prefixWord ++ tailWord_243301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243314 : List Nat := [3, 2, 1, 2, 3, 3, 2, 1, 5]
def baseStart_243314 : Nat := 118140960795 + 243314 * 2 ^ 59
def prefixEnd_243314 : Nat := 4983230072969 + 3 ^ 40 * 243314 * 2
def baseEnd_243314 : Nat := 27763784881814725901339

theorem tailTrace_243314 : CollatzResearch.WordTrace tailWord_243314 prefixEnd_243314 27763784881814725901339 := by
  unfold tailWord_243314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2218597660130601891992249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5916260427014938378645997 2218597660130601891992249)
  ·
    refine ⟨1663948245097951418994187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2218597660130601891992249 1663948245097951418994187)
    ·
      refine ⟨2495922367646927128491281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1663948245097951418994187 2495922367646927128491281)
      ·
        refine ⟨1871941775735195346368461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2495922367646927128491281 1871941775735195346368461)
        ·
          refine ⟨701978165900698254888173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1871941775735195346368461 701978165900698254888173)
          ·
            refine ⟨263241812212761845583065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 701978165900698254888173 263241812212761845583065)
            ·
              refine ⟨197431359159571384187299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263241812212761845583065 197431359159571384187299)
              ·
                refine ⟨296147038739357076280949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197431359159571384187299 296147038739357076280949)
                ·
                  refine ⟨27763784881814725901339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 296147038739357076280949 27763784881814725901339)
                  ·
                    rfl

theorem cell22_243314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_243314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243314 prefixEnd_243314 := by exact prefixLift 243314
  have htrace : WordTrace (prefixWord ++ tailWord_243314) baseStart_243314 baseEnd_243314 := by
    simpa [prefixWord, tailWord_243314, baseEnd_243314] using wordTrace_append hprefix tailTrace_243314
  have hstable : (prefixWord ++ tailWord_243314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243314).length < 2 ^ (prefixWord ++ tailWord_243314).sum := by decide
  have hdescent : baseEnd_243314 < baseStart_243314 := by decide
  rcases family_descends (prefixWord ++ tailWord_243314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243340 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_243340 : Nat := 118140960795 + 243340 * 2 ^ 59
def prefixEnd_243340 : Nat := 4983230072969 + 3 ^ 40 * 243340 * 2
def baseEnd_243340 : Nat := 83300254976788776553937

theorem tailTrace_243340 : CollatzResearch.WordTrace tailWord_243340 prefixEnd_243340 83300254976788776553937 := by
  unfold tailWord_243340
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437669469214107004207737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5916892625618809338943649 4437669469214107004207737)
  ·
    refine ⟨3328252101910580253155803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4437669469214107004207737 3328252101910580253155803)
    ·
      refine ⟨4992378152865870379733705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3328252101910580253155803 4992378152865870379733705)
      ·
        refine ⟨3744283614649402784800279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4992378152865870379733705 3744283614649402784800279)
        ·
          refine ⟨5616425421974104177200419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3744283614649402784800279 5616425421974104177200419)
          ·
            refine ⟨8424638132961156265800629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616425421974104177200419 8424638132961156265800629)
            ·
              refine ⟨789809824965108399918809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8424638132961156265800629 789809824965108399918809)
              ·
                refine ⟨592357368723831299939107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 789809824965108399918809 592357368723831299939107)
                ·
                  refine ⟨888536053085746949908661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592357368723831299939107 888536053085746949908661)
                  ·
                    refine ⟨83300254976788776553937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 888536053085746949908661 83300254976788776553937)
                    ·
                      rfl

theorem cell22_243340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_243340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243340 prefixEnd_243340 := by exact prefixLift 243340
  have htrace : WordTrace (prefixWord ++ tailWord_243340) baseStart_243340 baseEnd_243340 := by
    simpa [prefixWord, tailWord_243340, baseEnd_243340] using wordTrace_append hprefix tailTrace_243340
  have hstable : (prefixWord ++ tailWord_243340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243340).length < 2 ^ (prefixWord ++ tailWord_243340).sum := by decide
  have hdescent : baseEnd_243340 < baseStart_243340 := by decide
  rcases family_descends (prefixWord ++ tailWord_243340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243415 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 7]
def baseStart_243415 : Nat := 118140960795 + 243415 * 2 ^ 59
def prefixEnd_243415 : Nat := 4983230072969 + 3 ^ 40 * 243415 * 2
def baseEnd_243415 : Nat := 27775309669837860309569

theorem tailTrace_243415 : CollatzResearch.WordTrace tailWord_243415 prefixEnd_243415 27775309669837860309569 := by
  unfold tailWord_243415
  simp only [CollatzResearch.WordTrace]
  refine ⟨8878074413156501817395699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5918716275437667878263799 8878074413156501817395699)
  ·
    refine ⟨13317111619734752726093549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8878074413156501817395699 13317111619734752726093549)
    ·
      refine ⟨4993916857400532272285081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13317111619734752726093549 4993916857400532272285081)
      ·
        refine ⟨3745437643050399204213811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4993916857400532272285081 3745437643050399204213811)
        ·
          refine ⟨5618156464575598806320717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3745437643050399204213811 5618156464575598806320717)
          ·
            refine ⟨2106808674215849552370269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5618156464575598806320717 2106808674215849552370269)
            ·
              refine ⟨790053252830943582138851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2106808674215849552370269 790053252830943582138851)
              ·
                refine ⟨1185079879246415373208277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790053252830943582138851 1185079879246415373208277)
                ·
                  refine ⟨27775309669837860309569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1185079879246415373208277 27775309669837860309569)
                  ·
                    rfl

theorem cell22_243415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 7].length) (baseStart_243415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243415 prefixEnd_243415 := by exact prefixLift 243415
  have htrace : WordTrace (prefixWord ++ tailWord_243415) baseStart_243415 baseEnd_243415 := by
    simpa [prefixWord, tailWord_243415, baseEnd_243415] using wordTrace_append hprefix tailTrace_243415
  have hstable : (prefixWord ++ tailWord_243415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243415).length < 2 ^ (prefixWord ++ tailWord_243415).sum := by decide
  have hdescent : baseEnd_243415 < baseStart_243415 := by decide
  rcases family_descends (prefixWord ++ tailWord_243415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243475 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 5, 5]
def baseStart_243475 : Nat := 118140960795 + 243475 * 2 ^ 59
def prefixEnd_243475 : Nat := 4983230072969 + 3 ^ 40 * 243475 * 2
def baseEnd_243475 : Nat := 83346468235693424428523

theorem tailTrace_243475 : CollatzResearch.WordTrace tailWord_243475 prefixEnd_243475 83346468235693424428523 := by
  unfold tailWord_243475
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880262792939132064579879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5920175195292754709719919 8880262792939132064579879)
  ·
    refine ⟨13320394189408698096869819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8880262792939132064579879 13320394189408698096869819)
    ·
      refine ⟨19980591284113047145304729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13320394189408698096869819 19980591284113047145304729)
      ·
        refine ⟨14985443463084785358978547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19980591284113047145304729 14985443463084785358978547)
        ·
          refine ⟨22478165194627178038467821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14985443463084785358978547 22478165194627178038467821)
          ·
            refine ⟨8429311947985191764425433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22478165194627178038467821 8429311947985191764425433)
            ·
              refine ⟨6321983960988893823319075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8429311947985191764425433 6321983960988893823319075)
              ·
                refine ⟨9482975941483340734978613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321983960988893823319075 9482975941483340734978613)
                ·
                  refine ⟨889028994514063193904245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9482975941483340734978613 889028994514063193904245)
                  ·
                    refine ⟨83346468235693424428523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 889028994514063193904245 83346468235693424428523)
                    ·
                      rfl

theorem cell22_243475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 5].length) (baseStart_243475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243475 prefixEnd_243475 := by exact prefixLift 243475
  have htrace : WordTrace (prefixWord ++ tailWord_243475) baseStart_243475 baseEnd_243475 := by
    simpa [prefixWord, tailWord_243475, baseEnd_243475] using wordTrace_append hprefix tailTrace_243475
  have hstable : (prefixWord ++ tailWord_243475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243475).length < 2 ^ (prefixWord ++ tailWord_243475).sum := by decide
  have hdescent : baseEnd_243475 < baseStart_243475 := by decide
  rcases family_descends (prefixWord ++ tailWord_243475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243477 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 6]
def baseStart_243477 : Nat := 118140960795 + 243477 * 2 ^ 59
def prefixEnd_243477 : Nat := 4983230072969 + 3 ^ 40 * 243477 * 2
def baseEnd_243477 : Nat := 27782384292188695292839

theorem tailTrace_243477 : CollatzResearch.WordTrace tailWord_243477 prefixEnd_243477 27782384292188695292839 := by
  unfold tailWord_243477
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880335738931886406152685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5920223825954590937435123 8880335738931886406152685)
  ·
    refine ⟨3330125902099457402307257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8880335738931886406152685 3330125902099457402307257)
    ·
      refine ⟨2497594426574593051730443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3330125902099457402307257 2497594426574593051730443)
      ·
        refine ⟨3746391639861889577595665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2497594426574593051730443 3746391639861889577595665)
        ·
          refine ⟨2809793729896417183196749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3746391639861889577595665 2809793729896417183196749)
          ·
            refine ⟨1053672648711156443698781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2809793729896417183196749 1053672648711156443698781)
            ·
              refine ⟨395127243266683666387043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1053672648711156443698781 395127243266683666387043)
              ·
                refine ⟨592690864900025499580565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395127243266683666387043 592690864900025499580565)
                ·
                  refine ⟨27782384292188695292839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 592690864900025499580565 27782384292188695292839)
                  ·
                    rfl

theorem cell22_243477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_243477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243477 prefixEnd_243477 := by exact prefixLift 243477
  have htrace : WordTrace (prefixWord ++ tailWord_243477) baseStart_243477 baseEnd_243477 := by
    simpa [prefixWord, tailWord_243477, baseEnd_243477] using wordTrace_append hprefix tailTrace_243477
  have hstable : (prefixWord ++ tailWord_243477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243477).length < 2 ^ (prefixWord ++ tailWord_243477).sum := by decide
  have hdescent : baseEnd_243477 < baseStart_243477 := by decide
  rcases family_descends (prefixWord ++ tailWord_243477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243496 : List Nat := [2, 1, 5, 1, 1, 4, 1, 2, 1, 4]
def baseStart_243496 : Nat := 118140960795 + 243496 * 2 ^ 59
def prefixEnd_243496 : Nat := 4983230072969 + 3 ^ 40 * 243496 * 2
def baseEnd_243496 : Nat := 83353656964856369653459

theorem tailTrace_243496 : CollatzResearch.WordTrace tailWord_243496 prefixEnd_243496 83353656964856369653459 := by
  unfold tailWord_243496
  simp only [CollatzResearch.WordTrace]
  refine ⟨4440514362931526325547171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5920685817242035100729561 4440514362931526325547171)
  ·
    refine ⟨6660771544397289488320757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4440514362931526325547171 6660771544397289488320757)
    ·
      refine ⟨624447332287245889530071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6660771544397289488320757 624447332287245889530071)
      ·
        refine ⟨936670998430868834295107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624447332287245889530071 936670998430868834295107)
        ·
          refine ⟨1405006497646303251442661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936670998430868834295107 1405006497646303251442661)
          ·
            refine ⟨263438718308681859645499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1405006497646303251442661 263438718308681859645499)
            ·
              refine ⟨395158077463022789468249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263438718308681859645499 395158077463022789468249)
              ·
                refine ⟨296368558097267092101187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395158077463022789468249 296368558097267092101187)
                ·
                  refine ⟨444552837145900638151781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296368558097267092101187 444552837145900638151781)
                  ·
                    refine ⟨83353656964856369653459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 444552837145900638151781 83353656964856369653459)
                    ·
                      rfl

theorem cell22_243496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_243496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243496 prefixEnd_243496 := by exact prefixLift 243496
  have htrace : WordTrace (prefixWord ++ tailWord_243496) baseStart_243496 baseEnd_243496 := by
    simpa [prefixWord, tailWord_243496, baseEnd_243496] using wordTrace_append hprefix tailTrace_243496
  have hstable : (prefixWord ++ tailWord_243496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243496).length < 2 ^ (prefixWord ++ tailWord_243496).sum := by decide
  have hdescent : baseEnd_243496 < baseStart_243496 := by decide
  rcases family_descends (prefixWord ++ tailWord_243496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243509 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_243509 : Nat := 118140960795 + 243509 * 2 ^ 59
def prefixEnd_243509 : Nat := 4983230072969 + 3 ^ 40 * 243509 * 2
def baseEnd_243509 : Nat := 83358107130528669078419

theorem tailTrace_243509 : CollatzResearch.WordTrace tailWord_243509 prefixEnd_243509 83358107130528669078419 := by
  unfold tailWord_243509
  simp only [CollatzResearch.WordTrace]
  refine ⟨8881502874815955871317581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5921001916543970580878387 8881502874815955871317581)
  ·
    refine ⟨3330563578055983451744093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8881502874815955871317581 3330563578055983451744093)
    ·
      refine ⟨1248961341770993794404035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3330563578055983451744093 1248961341770993794404035)
      ·
        refine ⟨1873442012656490691606053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1248961341770993794404035 1873442012656490691606053)
        ·
          refine ⟨351270377373092004676135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1873442012656490691606053 351270377373092004676135)
          ·
            refine ⟨526905566059638007014203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351270377373092004676135 526905566059638007014203)
            ·
              refine ⟨790358349089457010521305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526905566059638007014203 790358349089457010521305)
              ·
                refine ⟨592768761817092757890979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790358349089457010521305 592768761817092757890979)
                ·
                  refine ⟨889153142725639136836469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592768761817092757890979 889153142725639136836469)
                  ·
                    refine ⟨83358107130528669078419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 889153142725639136836469 83358107130528669078419)
                    ·
                      rfl

theorem cell22_243509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_243509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243509 prefixEnd_243509 := by exact prefixLift 243509
  have htrace : WordTrace (prefixWord ++ tailWord_243509) baseStart_243509 baseEnd_243509 := by
    simpa [prefixWord, tailWord_243509, baseEnd_243509] using wordTrace_append hprefix tailTrace_243509
  have hstable : (prefixWord ++ tailWord_243509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243509).length < 2 ^ (prefixWord ++ tailWord_243509).sum := by decide
  have hdescent : baseEnd_243509 < baseStart_243509 := by decide
  rcases family_descends (prefixWord ++ tailWord_243509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243513 : List Nat := [1, 2, 1, 7, 1, 1, 3, 1, 1, 4]
def baseStart_243513 : Nat := 118140960795 + 243513 * 2 ^ 59
def prefixEnd_243513 : Nat := 4983230072969 + 3 ^ 40 * 243513 * 2
def baseEnd_243513 : Nat := 83359476412273991978407

theorem tailTrace_243513 : CollatzResearch.WordTrace tailWord_243513 prefixEnd_243513 83359476412273991978407 := by
  unfold tailWord_243513
  simp only [CollatzResearch.WordTrace]
  refine ⟨8881648766801464554463193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5921099177867643036308795 8881648766801464554463193)
  ·
    refine ⟨6661236575101098415847395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8881648766801464554463193 6661236575101098415847395)
    ·
      refine ⟨9991854862651647623771093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6661236575101098415847395 9991854862651647623771093)
      ·
        refine ⟨234184098343397991182135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9991854862651647623771093 234184098343397991182135)
        ·
          refine ⟨351276147515096986773203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234184098343397991182135 351276147515096986773203)
          ·
            refine ⟨526914221272645480159805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351276147515096986773203 526914221272645480159805)
            ·
              refine ⟨197592832977242055059927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 526914221272645480159805 197592832977242055059927)
              ·
                refine ⟨296389249465863082589891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197592832977242055059927 296389249465863082589891)
                ·
                  refine ⟨444583874198794623884837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296389249465863082589891 444583874198794623884837)
                  ·
                    refine ⟨83359476412273991978407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 444583874198794623884837 83359476412273991978407)
                    ·
                      rfl

theorem cell22_243513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 1, 4].length) (baseStart_243513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243513 prefixEnd_243513 := by exact prefixLift 243513
  have htrace : WordTrace (prefixWord ++ tailWord_243513) baseStart_243513 baseEnd_243513 := by
    simpa [prefixWord, tailWord_243513, baseEnd_243513] using wordTrace_append hprefix tailTrace_243513
  have hstable : (prefixWord ++ tailWord_243513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243513).length < 2 ^ (prefixWord ++ tailWord_243513).sum := by decide
  have hdescent : baseEnd_243513 < baseStart_243513 := by decide
  rcases family_descends (prefixWord ++ tailWord_243513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243642 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_243642 : Nat := 118140960795 + 243642 * 2 ^ 59
def prefixEnd_243642 : Nat := 4983230072969 + 3 ^ 40 * 243642 * 2
def baseEnd_243642 : Nat := 83403635748560655503011

theorem tailTrace_243642 : CollatzResearch.WordTrace tailWord_243642 prefixEnd_243642 83403635748560655503011 := by
  unfold tailWord_243642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2221588445833529896477295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5924235855556079723939453 2221588445833529896477295)
  ·
    refine ⟨3332382668750294844715943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2221588445833529896477295 3332382668750294844715943)
    ·
      refine ⟨4998574003125442267073915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3332382668750294844715943 4998574003125442267073915)
      ·
        refine ⟨7497861004688163400610873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4998574003125442267073915 7497861004688163400610873)
        ·
          refine ⟨5623395753516122550458155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7497861004688163400610873 5623395753516122550458155)
          ·
            refine ⟨8435093630274183825687233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5623395753516122550458155 8435093630274183825687233)
            ·
              refine ⟨6326320222705637869265425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8435093630274183825687233 6326320222705637869265425)
              ·
                refine ⟨4744740167029228401949069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6326320222705637869265425 4744740167029228401949069)
                ·
                  refine ⟨1779277562635960650730901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4744740167029228401949069 1779277562635960650730901)
                  ·
                    refine ⟨83403635748560655503011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1779277562635960650730901 83403635748560655503011)
                    ·
                      rfl

theorem cell22_243642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_243642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243642 prefixEnd_243642 := by exact prefixLift 243642
  have htrace : WordTrace (prefixWord ++ tailWord_243642) baseStart_243642 baseEnd_243642 := by
    simpa [prefixWord, tailWord_243642, baseEnd_243642] using wordTrace_append hprefix tailTrace_243642
  have hstable : (prefixWord ++ tailWord_243642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243642).length < 2 ^ (prefixWord ++ tailWord_243642).sum := by decide
  have hdescent : baseEnd_243642 < baseStart_243642 := by decide
  rcases family_descends (prefixWord ++ tailWord_243642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243646 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_243646 : Nat := 118140960795 + 243646 * 2 ^ 59
def prefixEnd_243646 : Nat := 4983230072969 + 3 ^ 40 * 243646 * 2
def baseEnd_243646 : Nat := 27801668343435326134333

theorem tailTrace_243646 : CollatzResearch.WordTrace tailWord_243646 prefixEnd_243646 27801668343435326134333 := by
  unfold tailWord_243646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110812459414953533631849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5924333116879752179369861 1110812459414953533631849)
  ·
    refine ⟨833109344561215150223887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1110812459414953533631849 833109344561215150223887)
    ·
      refine ⟨1249664016841822725335831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 833109344561215150223887 1249664016841822725335831)
      ·
        refine ⟨1874496025262734088003747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249664016841822725335831 1874496025262734088003747)
        ·
          refine ⟨2811744037894101132005621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874496025262734088003747 2811744037894101132005621)
          ·
            refine ⟨263601003552571981125527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2811744037894101132005621 263601003552571981125527)
            ·
              refine ⟨395401505328857971688291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263601003552571981125527 395401505328857971688291)
              ·
                refine ⟨593102257993286957532437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395401505328857971688291 593102257993286957532437)
                ·
                  refine ⟨27801668343435326134333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 593102257993286957532437 27801668343435326134333)
                  ·
                    rfl

theorem cell22_243646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_243646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243646 prefixEnd_243646 := by exact prefixLift 243646
  have htrace : WordTrace (prefixWord ++ tailWord_243646) baseStart_243646 baseEnd_243646 := by
    simpa [prefixWord, tailWord_243646, baseEnd_243646] using wordTrace_append hprefix tailTrace_243646
  have hstable : (prefixWord ++ tailWord_243646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243646).length < 2 ^ (prefixWord ++ tailWord_243646).sum := by decide
  have hdescent : baseEnd_243646 < baseStart_243646 := by decide
  rcases family_descends (prefixWord ++ tailWord_243646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243740 : List Nat := [2, 2, 3, 1, 3, 2, 2, 3, 1, 3]
def baseStart_243740 : Nat := 118140960795 + 243740 * 2 ^ 59
def prefixEnd_243740 : Nat := 4983230072969 + 3 ^ 40 * 243740 * 2
def baseEnd_243740 : Nat := 83437183151321066552711

theorem tailTrace_243740 : CollatzResearch.WordTrace tailWord_243740 prefixEnd_243740 83437183151321066552711 := by
  unfold tailWord_243740
  simp only [CollatzResearch.WordTrace]
  refine ⟨4444964068489541161488337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5926618757986054881984449 4444964068489541161488337)
  ·
    refine ⟨3333723051367155871116253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4444964068489541161488337 3333723051367155871116253)
    ·
      refine ⟨1250146144262683451668595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3333723051367155871116253 1250146144262683451668595)
      ·
        refine ⟨1875219216394025177502893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250146144262683451668595 1875219216394025177502893)
        ·
          refine ⟨703207206147759441563585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1875219216394025177502893 703207206147759441563585)
          ·
            refine ⟨527405404610819581172689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 703207206147759441563585 527405404610819581172689)
            ·
              refine ⟨395554053458114685879517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527405404610819581172689 395554053458114685879517)
              ·
                refine ⟨148332770046793007204819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395554053458114685879517 148332770046793007204819)
                ·
                  refine ⟨222499155070189510807229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148332770046793007204819 222499155070189510807229)
                  ·
                    refine ⟨83437183151321066552711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 222499155070189510807229 83437183151321066552711)
                    ·
                      rfl

theorem cell22_243740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_243740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243740 prefixEnd_243740 := by exact prefixLift 243740
  have htrace : WordTrace (prefixWord ++ tailWord_243740) baseStart_243740 baseEnd_243740 := by
    simpa [prefixWord, tailWord_243740, baseEnd_243740] using wordTrace_append hprefix tailTrace_243740
  have hstable : (prefixWord ++ tailWord_243740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243740).length < 2 ^ (prefixWord ++ tailWord_243740).sum := by decide
  have hdescent : baseEnd_243740 < baseStart_243740 := by decide
  rcases family_descends (prefixWord ++ tailWord_243740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243779 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 1, 5]
def baseStart_243779 : Nat := 118140960795 + 243779 * 2 ^ 59
def prefixEnd_243779 : Nat := 4983230072969 + 3 ^ 40 * 243779 * 2
def baseEnd_243779 : Nat := 83450533648337964827591

theorem tailTrace_243779 : CollatzResearch.WordTrace tailWord_243779 prefixEnd_243779 83450533648337964827591 := by
  unfold tailWord_243779
  simp only [CollatzResearch.WordTrace]
  refine ⟨8891350583837791983646391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5927567055891861322430927 8891350583837791983646391)
  ·
    refine ⟨13337025875756687975469587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8891350583837791983646391 13337025875756687975469587)
    ·
      refine ⟨20005538813635031963204381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13337025875756687975469587 20005538813635031963204381)
      ·
        refine ⟨7502077055113136986201643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20005538813635031963204381 7502077055113136986201643)
        ·
          refine ⟨11253115582669705479302465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502077055113136986201643 11253115582669705479302465)
          ·
            refine ⟨8439836687002279109476849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11253115582669705479302465 8439836687002279109476849)
            ·
              refine ⟨6329877515251709332107637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8439836687002279109476849 6329877515251709332107637)
              ·
                refine ⟨593426017054847749885091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6329877515251709332107637 593426017054847749885091)
                ·
                  refine ⟨890139025582271624827637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593426017054847749885091 890139025582271624827637)
                  ·
                    refine ⟨83450533648337964827591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 890139025582271624827637 83450533648337964827591)
                    ·
                      rfl

theorem cell22_243779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 5].length) (baseStart_243779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243779 prefixEnd_243779 := by exact prefixLift 243779
  have htrace : WordTrace (prefixWord ++ tailWord_243779) baseStart_243779 baseEnd_243779 := by
    simpa [prefixWord, tailWord_243779, baseEnd_243779] using wordTrace_append hprefix tailTrace_243779
  have hstable : (prefixWord ++ tailWord_243779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243779).length < 2 ^ (prefixWord ++ tailWord_243779).sum := by decide
  have hdescent : baseEnd_243779 < baseStart_243779 := by decide
  rcases family_descends (prefixWord ++ tailWord_243779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243826 : List Nat := [3, 2, 1, 2, 2, 3, 2, 7]
def baseStart_243826 : Nat := 118140960795 + 243826 * 2 ^ 59
def prefixEnd_243826 : Nat := 4983230072969 + 3 ^ 40 * 243826 * 2
def baseEnd_243826 : Nat := 9274069189871723211383

theorem tailTrace_243826 : CollatzResearch.WordTrace tailWord_243826 prefixEnd_243826 9274069189871723211383 := by
  unfold tailWord_243826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223266203666879752651833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5928709876445012673738221 2223266203666879752651833)
  ·
    refine ⟨1667449652750159814488875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2223266203666879752651833 1667449652750159814488875)
    ·
      refine ⟨2501174479125239721733313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1667449652750159814488875 2501174479125239721733313)
      ·
        refine ⟨1875880859343929791299985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2501174479125239721733313 1875880859343929791299985)
        ·
          refine ⟨1406910644507947343474989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1875880859343929791299985 1406910644507947343474989)
          ·
            refine ⟨527591491690480253803121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1406910644507947343474989 527591491690480253803121)
            ·
              refine ⟨395693618767860190352341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527591491690480253803121 395693618767860190352341)
              ·
                refine ⟨9274069189871723211383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 395693618767860190352341 9274069189871723211383)
                ·
                  rfl

theorem cell22_243826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_243826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243826 prefixEnd_243826 := by exact prefixLift 243826
  have htrace : WordTrace (prefixWord ++ tailWord_243826) baseStart_243826 baseEnd_243826 := by
    simpa [prefixWord, tailWord_243826, baseEnd_243826] using wordTrace_append hprefix tailTrace_243826
  have hstable : (prefixWord ++ tailWord_243826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243826).length < 2 ^ (prefixWord ++ tailWord_243826).sum := by decide
  have hdescent : baseEnd_243826 < baseStart_243826 := by decide
  rcases family_descends (prefixWord ++ tailWord_243826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243830 : List Nat := [5, 1, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_243830 : Nat := 118140960795 + 243830 * 2 ^ 59
def prefixEnd_243830 : Nat := 4983230072969 + 3 ^ 40 * 243830 * 2
def baseEnd_243830 : Nat := 83467991990590831802435

theorem tailTrace_243830 : CollatzResearch.WordTrace tailWord_243830 prefixEnd_243830 83467991990590831802435 := by
  unfold tailWord_243830
  simp only [CollatzResearch.WordTrace]
  refine ⟨555825669165814230859559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5928807137768685129168629 555825669165814230859559)
  ·
    refine ⟨833738503748721346289339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 555825669165814230859559 833738503748721346289339)
    ·
      refine ⟨1250607755623082019434009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 833738503748721346289339 1250607755623082019434009)
      ·
        refine ⟨937955816717311514575507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1250607755623082019434009 937955816717311514575507)
        ·
          refine ⟨1406933725075967271863261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 937955816717311514575507 1406933725075967271863261)
          ·
            refine ⟨527600146903487726948723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1406933725075967271863261 527600146903487726948723)
            ·
              refine ⟨791400220355231590423085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527600146903487726948723 791400220355231590423085)
              ·
                refine ⟨296775082633211846408657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 791400220355231590423085 296775082633211846408657)
                ·
                  refine ⟨222581311974908884806493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296775082633211846408657 222581311974908884806493)
                  ·
                    refine ⟨83467991990590831802435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 222581311974908884806493 83467991990590831802435)
                    ·
                      rfl

theorem cell22_243830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_243830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243830 prefixEnd_243830 := by exact prefixLift 243830
  have htrace : WordTrace (prefixWord ++ tailWord_243830) baseStart_243830 baseEnd_243830 := by
    simpa [prefixWord, tailWord_243830, baseEnd_243830] using wordTrace_append hprefix tailTrace_243830
  have hstable : (prefixWord ++ tailWord_243830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243830).length < 2 ^ (prefixWord ++ tailWord_243830).sum := by decide
  have hdescent : baseEnd_243830 < baseStart_243830 := by decide
  rcases family_descends (prefixWord ++ tailWord_243830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243933 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 6]
def baseStart_243933 : Nat := 118140960795 + 243933 * 2 ^ 59
def prefixEnd_243933 : Nat := 4983230072969 + 3 ^ 40 * 243933 * 2
def baseEnd_243933 : Nat := 27834416998510965492373

theorem tailTrace_243933 : CollatzResearch.WordTrace tailWord_243933 prefixEnd_243933 27834416998510965492373 := by
  unfold tailWord_243933
  simp only [CollatzResearch.WordTrace]
  refine ⟨8896967425279876284752453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5931311616853250856501635 8896967425279876284752453)
  ·
    refine ⟨1668181392239976803391085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8896967425279876284752453 1668181392239976803391085)
    ·
      refine ⟨625568022089991301271657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1668181392239976803391085 625568022089991301271657)
      ·
        refine ⟨469176016567493475953743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625568022089991301271657 469176016567493475953743)
        ·
          refine ⟨703764024851240213930615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469176016567493475953743 703764024851240213930615)
          ·
            refine ⟨1055646037276860320895923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703764024851240213930615 1055646037276860320895923)
            ·
              refine ⟨1583469055915290481343885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055646037276860320895923 1583469055915290481343885)
              ·
                refine ⟨593800895968233930503957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1583469055915290481343885 593800895968233930503957)
                ·
                  refine ⟨27834416998510965492373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 593800895968233930503957 27834416998510965492373)
                  ·
                    rfl

theorem cell22_243933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_243933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243933 prefixEnd_243933 := by exact prefixLift 243933
  have htrace : WordTrace (prefixWord ++ tailWord_243933) baseStart_243933 baseEnd_243933 := by
    simpa [prefixWord, tailWord_243933, baseEnd_243933] using wordTrace_append hprefix tailTrace_243933
  have hstable : (prefixWord ++ tailWord_243933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243933).length < 2 ^ (prefixWord ++ tailWord_243933).sum := by decide
  have hdescent : baseEnd_243933 < baseStart_243933 := by decide
  rcases family_descends (prefixWord ++ tailWord_243933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243946 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_243946 : Nat := 118140960795 + 243946 * 2 ^ 59
def prefixEnd_243946 : Nat := 4983230072969 + 3 ^ 40 * 243946 * 2
def baseEnd_243946 : Nat := 83507701161205195902079

theorem tailTrace_243946 : CollatzResearch.WordTrace tailWord_243946 prefixEnd_243946 83507701161205195902079 := by
  unfold tailWord_243946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2224360393558194876243923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5931627716155186336650461 2224360393558194876243923)
  ·
    refine ⟨3336540590337292314365885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2224360393558194876243923 3336540590337292314365885)
    ·
      refine ⟨1251202721376484617887207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3336540590337292314365885 1251202721376484617887207)
      ·
        refine ⟨1876804082064726926830811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251202721376484617887207 1876804082064726926830811)
        ·
          refine ⟨2815206123097090390246217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876804082064726926830811 2815206123097090390246217)
          ·
            refine ⟨2111404592322817792684663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2815206123097090390246217 2111404592322817792684663)
            ·
              refine ⟨3167106888484226689026995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2111404592322817792684663 3167106888484226689026995)
              ·
                refine ⟨4750660332726340033540493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3167106888484226689026995 4750660332726340033540493)
                ·
                  refine ⟨1781497624772377512577685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4750660332726340033540493 1781497624772377512577685)
                  ·
                    refine ⟨83507701161205195902079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1781497624772377512577685 83507701161205195902079)
                    ·
                      rfl

theorem cell22_243946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_243946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_243946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_243946 prefixEnd_243946 := by exact prefixLift 243946
  have htrace : WordTrace (prefixWord ++ tailWord_243946) baseStart_243946 baseEnd_243946 := by
    simpa [prefixWord, tailWord_243946, baseEnd_243946] using wordTrace_append hprefix tailTrace_243946
  have hstable : (prefixWord ++ tailWord_243946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243946).length < 2 ^ (prefixWord ++ tailWord_243946).sum := by decide
  have hdescent : baseEnd_243946 < baseStart_243946 := by decide
  rcases family_descends (prefixWord ++ tailWord_243946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244068 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 6]
def baseStart_244068 : Nat := 118140960795 + 244068 * 2 ^ 59
def prefixEnd_244068 : Nat := 4983230072969 + 3 ^ 40 * 244068 * 2
def baseEnd_244068 : Nat := 27849821418145848117235

theorem tailTrace_244068 : CollatzResearch.WordTrace tailWord_244068 prefixEnd_244068 27849821418145848117235 := by
  unfold tailWord_244068
  simp only [CollatzResearch.WordTrace]
  refine ⟨4450945639895397170458429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5934594186527196227277905 4450945639895397170458429)
  ·
    refine ⟨1669104614960773938921911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4450945639895397170458429 1669104614960773938921911)
    ·
      refine ⟨2503656922441160908382867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1669104614960773938921911 2503656922441160908382867)
      ·
        refine ⟨3755485383661741362574301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503656922441160908382867 3755485383661741362574301)
        ·
          refine ⟨1408307018873153010965363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3755485383661741362574301 1408307018873153010965363)
          ·
            refine ⟨2112460528309729516448045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408307018873153010965363 2112460528309729516448045)
            ·
              refine ⟨792172698116148568668017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2112460528309729516448045 792172698116148568668017)
              ·
                refine ⟨594129523587111426501013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792172698116148568668017 594129523587111426501013)
                ·
                  refine ⟨27849821418145848117235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 594129523587111426501013 27849821418145848117235)
                  ·
                    rfl

theorem cell22_244068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_244068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244068 prefixEnd_244068 := by exact prefixLift 244068
  have htrace : WordTrace (prefixWord ++ tailWord_244068) baseStart_244068 baseEnd_244068 := by
    simpa [prefixWord, tailWord_244068, baseEnd_244068] using wordTrace_append hprefix tailTrace_244068
  have hstable : (prefixWord ++ tailWord_244068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244068).length < 2 ^ (prefixWord ++ tailWord_244068).sum := by decide
  have hdescent : baseEnd_244068 < baseStart_244068 := by decide
  rcases family_descends (prefixWord ++ tailWord_244068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244083 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 6, 3]
def baseStart_244083 : Nat := 118140960795 + 244083 * 2 ^ 59
def prefixEnd_244083 : Nat := 4983230072969 + 3 ^ 40 * 244083 * 2
def baseEnd_244083 : Nat := 83554599060982505226659

theorem tailTrace_244083 : CollatzResearch.WordTrace tailWord_244083 prefixEnd_244083 83554599060982505226659 := by
  unfold tailWord_244083
  simp only [CollatzResearch.WordTrace]
  refine ⟨8902438374736451902712903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5934958916490967935141935 8902438374736451902712903)
  ·
    refine ⟨13353657562104677854069355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8902438374736451902712903 13353657562104677854069355)
    ·
      refine ⟨20030486343157016781104033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13353657562104677854069355 20030486343157016781104033)
      ·
        refine ⟨15022864757367762585828025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20030486343157016781104033 15022864757367762585828025)
        ·
          refine ⟨11267148568025821939371019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15022864757367762585828025 11267148568025821939371019)
          ·
            refine ⟨16900722852038732909056529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11267148568025821939371019 16900722852038732909056529)
            ·
              refine ⟨12675542139029049681792397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16900722852038732909056529 12675542139029049681792397)
              ·
                refine ⟨4753328302135893630672149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12675542139029049681792397 4753328302135893630672149)
                ·
                  refine ⟨222812264162620013937757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4753328302135893630672149 222812264162620013937757)
                  ·
                    refine ⟨83554599060982505226659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 222812264162620013937757 83554599060982505226659)
                    ·
                      rfl

theorem cell22_244083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 3].length) (baseStart_244083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244083 prefixEnd_244083 := by exact prefixLift 244083
  have htrace : WordTrace (prefixWord ++ tailWord_244083) baseStart_244083 baseEnd_244083 := by
    simpa [prefixWord, tailWord_244083, baseEnd_244083] using wordTrace_append hprefix tailTrace_244083
  have hstable : (prefixWord ++ tailWord_244083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244083).length < 2 ^ (prefixWord ++ tailWord_244083).sum := by decide
  have hdescent : baseEnd_244083 < baseStart_244083 := by decide
  rcases family_descends (prefixWord ++ tailWord_244083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244100 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_244100 : Nat := 118140960795 + 244100 * 2 ^ 59
def prefixEnd_244100 : Nat := 4983230072969 + 3 ^ 40 * 244100 * 2
def baseEnd_244100 : Nat := 83560418508400127551607

theorem tailTrace_244100 : CollatzResearch.WordTrace tailWord_244100 prefixEnd_244100 83560418508400127551607 := by
  unfold tailWord_244100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4451529207837431903040877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5935372277116575870721169 4451529207837431903040877)
  ·
    refine ⟨1669323452939036963640329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4451529207837431903040877 1669323452939036963640329)
    ·
      refine ⟨1251992589704277722730247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1669323452939036963640329 1251992589704277722730247)
      ·
        refine ⟨1877988884556416584095371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251992589704277722730247 1877988884556416584095371)
        ·
          refine ⟨2816983326834624876143057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877988884556416584095371 2816983326834624876143057)
          ·
            refine ⟨2112737495125968657107293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2816983326834624876143057 2112737495125968657107293)
            ·
              refine ⟨792276560672238246415235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2112737495125968657107293 792276560672238246415235)
              ·
                refine ⟨1188414841008357369622853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792276560672238246415235 1188414841008357369622853)
                ·
                  refine ⟨222827782689067006804285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1188414841008357369622853 222827782689067006804285)
                  ·
                    refine ⟨83560418508400127551607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 222827782689067006804285 83560418508400127551607)
                    ·
                      rfl

theorem cell22_244100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_244100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244100 prefixEnd_244100 := by exact prefixLift 244100
  have htrace : WordTrace (prefixWord ++ tailWord_244100) baseStart_244100 baseEnd_244100 := by
    simpa [prefixWord, tailWord_244100, baseEnd_244100] using wordTrace_append hprefix tailTrace_244100
  have hstable : (prefixWord ++ tailWord_244100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244100).length < 2 ^ (prefixWord ++ tailWord_244100).sum := by decide
  have hdescent : baseEnd_244100 < baseStart_244100 := by decide
  rcases family_descends (prefixWord ++ tailWord_244100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244235 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 1, 5]
def baseStart_244235 : Nat := 118140960795 + 244235 * 2 ^ 59
def prefixEnd_244235 : Nat := 4983230072969 + 3 ^ 40 * 244235 * 2
def baseEnd_244235 : Nat := 83606631767304775426193

theorem tailTrace_244235 : CollatzResearch.WordTrace tailWord_244235 prefixEnd_244235 83606631767304775426193 := by
  unfold tailWord_244235
  simp only [CollatzResearch.WordTrace]
  refine ⟨8907982270185781862246159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5938654846790521241497439 8907982270185781862246159)
  ·
    refine ⟨13361973405278672793369239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8907982270185781862246159 13361973405278672793369239)
    ·
      refine ⟨20042960107918009190053859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13361973405278672793369239 20042960107918009190053859)
      ·
        refine ⟨30064440161877013785080789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20042960107918009190053859 30064440161877013785080789)
        ·
          refine ⟨704635316293992510587831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 30064440161877013785080789 704635316293992510587831)
          ·
            refine ⟨1056952974440988765881747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704635316293992510587831 1056952974440988765881747)
            ·
              refine ⟨1585429461661483148822621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056952974440988765881747 1585429461661483148822621)
              ·
                refine ⟨594536048123056180808483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1585429461661483148822621 594536048123056180808483)
                ·
                  refine ⟨891804072184584271212725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594536048123056180808483 891804072184584271212725)
                  ·
                    refine ⟨83606631767304775426193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 891804072184584271212725 83606631767304775426193)
                    ·
                      rfl

theorem cell22_244235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 5].length) (baseStart_244235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244235 prefixEnd_244235 := by exact prefixLift 244235
  have htrace : WordTrace (prefixWord ++ tailWord_244235) baseStart_244235 baseEnd_244235 := by
    simpa [prefixWord, tailWord_244235, baseEnd_244235] using wordTrace_append hprefix tailTrace_244235
  have hstable : (prefixWord ++ tailWord_244235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244235).length < 2 ^ (prefixWord ++ tailWord_244235).sum := by decide
  have hdescent : baseEnd_244235 < baseStart_244235 := by decide
  rcases family_descends (prefixWord ++ tailWord_244235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244256 : List Nat := [2, 1, 1, 6, 2, 2, 2, 1, 1, 4]
def baseStart_244256 : Nat := 118140960795 + 244256 * 2 ^ 59
def prefixEnd_244256 : Nat := 4983230072969 + 3 ^ 40 * 244256 * 2
def baseEnd_244256 : Nat := 83613820496467720651129

theorem tailTrace_244256 : CollatzResearch.WordTrace tailWord_244256 prefixEnd_244256 83613820496467720651129 := by
  unfold tailWord_244256
  simp only [CollatzResearch.WordTrace]
  refine ⟨4454374101554851224380311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5939165468739801632507081 4454374101554851224380311)
  ·
    refine ⟨6681561152332276836570467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4454374101554851224380311 6681561152332276836570467)
    ·
      refine ⟨10022341728498415254855701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6681561152332276836570467 10022341728498415254855701)
      ·
        refine ⟨469797268523363215071361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10022341728498415254855701 469797268523363215071361)
        ·
          refine ⟨352347951392522411303521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469797268523363215071361 352347951392522411303521)
          ·
            refine ⟨264260963544391808477641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352347951392522411303521 264260963544391808477641)
            ·
              refine ⟨198195722658293856358231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264260963544391808477641 198195722658293856358231)
              ·
                refine ⟨297293583987440784537347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198195722658293856358231 297293583987440784537347)
                ·
                  refine ⟨445940375981161176806021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297293583987440784537347 445940375981161176806021)
                  ·
                    refine ⟨83613820496467720651129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 445940375981161176806021 83613820496467720651129)
                    ·
                      rfl

theorem cell22_244256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 1, 4].length) (baseStart_244256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244256 prefixEnd_244256 := by exact prefixLift 244256
  have htrace : WordTrace (prefixWord ++ tailWord_244256) baseStart_244256 baseEnd_244256 := by
    simpa [prefixWord, tailWord_244256, baseEnd_244256] using wordTrace_append hprefix tailTrace_244256
  have hstable : (prefixWord ++ tailWord_244256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244256).length < 2 ^ (prefixWord ++ tailWord_244256).sum := by decide
  have hdescent : baseEnd_244256 < baseStart_244256 := by decide
  rcases family_descends (prefixWord ++ tailWord_244256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244286 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_244286 : Nat := 118140960795 + 244286 * 2 ^ 59
def prefixEnd_244286 : Nat := 4983230072969 + 3 ^ 40 * 244286 * 2
def baseEnd_244286 : Nat := 83624090109557642401037

theorem tailTrace_244286 : CollatzResearch.WordTrace tailWord_244286 prefixEnd_244286 83624090109557642401037 := by
  unfold tailWord_244286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113730299125127196544089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5939894928667345048235141 1113730299125127196544089)
  ·
    refine ⟨835297724343845397408067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1113730299125127196544089 835297724343845397408067)
    ·
      refine ⟨1252946586515768096112101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 835297724343845397408067 1252946586515768096112101)
      ·
        refine ⟨234927484971706518021019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1252946586515768096112101 234927484971706518021019)
        ·
          refine ⟨352391227457559777031529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234927484971706518021019 352391227457559777031529)
          ·
            refine ⟨264293420593169832773647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352391227457559777031529 264293420593169832773647)
            ·
              refine ⟨396440130889754749160471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264293420593169832773647 396440130889754749160471)
              ·
                refine ⟨594660196334632123740707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396440130889754749160471 594660196334632123740707)
                ·
                  refine ⟨891990294501948185611061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594660196334632123740707 891990294501948185611061)
                  ·
                    refine ⟨83624090109557642401037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 891990294501948185611061 83624090109557642401037)
                    ·
                      rfl

theorem cell22_244286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_244286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244286 prefixEnd_244286 := by exact prefixLift 244286
  have htrace : WordTrace (prefixWord ++ tailWord_244286) baseStart_244286 baseEnd_244286 := by
    simpa [prefixWord, tailWord_244286, baseEnd_244286] using wordTrace_append hprefix tailTrace_244286
  have hstable : (prefixWord ++ tailWord_244286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244286).length < 2 ^ (prefixWord ++ tailWord_244286).sum := by decide
  have hdescent : baseEnd_244286 < baseStart_244286 := by decide
  rcases family_descends (prefixWord ++ tailWord_244286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244318 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_244318 : Nat := 118140960795 + 244318 * 2 ^ 59
def prefixEnd_244318 : Nat := 4983230072969 + 3 ^ 40 * 244318 * 2
def baseEnd_244318 : Nat := 83635044363520225600939

theorem tailTrace_244318 : CollatzResearch.WordTrace tailWord_244318 prefixEnd_244318 83635044363520225600939 := by
  unfold tailWord_244318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113876191110635879689701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5940673019256724691678405 1113876191110635879689701)
  ·
    refine ⟨208851785833244227441819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1113876191110635879689701 208851785833244227441819)
    ·
      refine ⟨313277678749866341162729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208851785833244227441819 313277678749866341162729)
      ·
        refine ⟨234958259062399755872047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313277678749866341162729 234958259062399755872047)
        ·
          refine ⟨352437388593599633808071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234958259062399755872047 352437388593599633808071)
          ·
            refine ⟨528656082890399450712107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352437388593599633808071 528656082890399450712107)
            ·
              refine ⟨792984124335599176068161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528656082890399450712107 792984124335599176068161)
              ·
                refine ⟨594738093251699382051121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792984124335599176068161 594738093251699382051121)
                ·
                  refine ⟨446053569938774536538341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594738093251699382051121 446053569938774536538341)
                  ·
                    refine ⟨83635044363520225600939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 446053569938774536538341 83635044363520225600939)
                    ·
                      rfl

theorem cell22_244318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_244318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244318 prefixEnd_244318 := by exact prefixLift 244318
  have htrace : WordTrace (prefixWord ++ tailWord_244318) baseStart_244318 baseEnd_244318 := by
    simpa [prefixWord, tailWord_244318, baseEnd_244318] using wordTrace_append hprefix tailTrace_244318
  have hstable : (prefixWord ++ tailWord_244318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244318).length < 2 ^ (prefixWord ++ tailWord_244318).sum := by decide
  have hdescent : baseEnd_244318 < baseStart_244318 := by decide
  rcases family_descends (prefixWord ++ tailWord_244318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244355 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 6]
def baseStart_244355 : Nat := 118140960795 + 244355 * 2 ^ 59
def prefixEnd_244355 : Nat := 4983230072969 + 3 ^ 40 * 244355 * 2
def baseEnd_244355 : Nat := 27882570073221487475275

theorem tailTrace_244355 : CollatzResearch.WordTrace tailWord_244355 prefixEnd_244355 27882570073221487475275 := by
  unfold tailWord_244355
  simp only [CollatzResearch.WordTrace]
  refine ⟨8912359029751042356614519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5941572686500694904409679 8912359029751042356614519)
  ·
    refine ⟨13368538544626563534921779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8912359029751042356614519 13368538544626563534921779)
    ·
      refine ⟨20052807816939845302382669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13368538544626563534921779 20052807816939845302382669)
      ·
        refine ⟨7519802931352441988393501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20052807816939845302382669 7519802931352441988393501)
        ·
          refine ⟨2819926099257165745647563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7519802931352441988393501 2819926099257165745647563)
          ·
            refine ⟨4229889148885748618471345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819926099257165745647563 4229889148885748618471345)
            ·
              refine ⟨3172416861664311463853509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4229889148885748618471345 3172416861664311463853509)
              ·
                refine ⟨594828161562058399472533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3172416861664311463853509 594828161562058399472533)
                ·
                  refine ⟨27882570073221487475275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 594828161562058399472533 27882570073221487475275)
                  ·
                    rfl

theorem cell22_244355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 6].length) (baseStart_244355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244355 prefixEnd_244355 := by exact prefixLift 244355
  have htrace : WordTrace (prefixWord ++ tailWord_244355) baseStart_244355 baseEnd_244355 := by
    simpa [prefixWord, tailWord_244355, baseEnd_244355] using wordTrace_append hprefix tailTrace_244355
  have hstable : (prefixWord ++ tailWord_244355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244355).length < 2 ^ (prefixWord ++ tailWord_244355).sum := by decide
  have hdescent : baseEnd_244355 < baseStart_244355 := by decide
  rcases family_descends (prefixWord ++ tailWord_244355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244357 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_244357 : Nat := 118140960795 + 244357 * 2 ^ 59
def prefixEnd_244357 : Nat := 4983230072969 + 3 ^ 40 * 244357 * 2
def baseEnd_244357 : Nat := 83648394860537123875819

theorem tailTrace_244357 : CollatzResearch.WordTrace tailWord_244357 prefixEnd_244357 83648394860537123875819 := by
  unfold tailWord_244357
  simp only [CollatzResearch.WordTrace]
  refine ⟨8912431975743796698187325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5941621317162531132124883 8912431975743796698187325)
  ·
    refine ⟨3342161990903923761820247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8912431975743796698187325 3342161990903923761820247)
    ·
      refine ⟨5013242986355885642730371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3342161990903923761820247 5013242986355885642730371)
      ·
        refine ⟨7519864479533828464095557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5013242986355885642730371 7519864479533828464095557)
        ·
          refine ⟨1409974589912592837017917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7519864479533828464095557 1409974589912592837017917)
          ·
            refine ⟨528740471217222313881719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1409974589912592837017917 528740471217222313881719)
            ·
              refine ⟨793110706825833470822579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528740471217222313881719 793110706825833470822579)
              ·
                refine ⟨1189666060238750206233869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793110706825833470822579 1189666060238750206233869)
                ·
                  refine ⟨446124772589531327337701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189666060238750206233869 446124772589531327337701)
                  ·
                    refine ⟨83648394860537123875819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 446124772589531327337701 83648394860537123875819)
                    ·
                      rfl

theorem cell22_244357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_244357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244357 prefixEnd_244357 := by exact prefixLift 244357
  have htrace : WordTrace (prefixWord ++ tailWord_244357) baseStart_244357 baseEnd_244357 := by
    simpa [prefixWord, tailWord_244357, baseEnd_244357] using wordTrace_append hprefix tailTrace_244357
  have hstable : (prefixWord ++ tailWord_244357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244357).length < 2 ^ (prefixWord ++ tailWord_244357).sum := by decide
  have hdescent : baseEnd_244357 < baseStart_244357 := by decide
  rcases family_descends (prefixWord ++ tailWord_244357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244406 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_244406 : Nat := 118140960795 + 244406 * 2 ^ 59
def prefixEnd_244406 : Nat := 4983230072969 + 3 ^ 40 * 244406 * 2
def baseEnd_244406 : Nat := 27888389520639109800223

theorem tailTrace_244406 : CollatzResearch.WordTrace tailWord_244406 prefixEnd_244406 27888389520639109800223 := by
  unfold tailWord_244406
  simp only [CollatzResearch.WordTrace]
  refine ⟨557138697035392379170067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5942812768377518711147381 557138697035392379170067)
  ·
    refine ⟨835708045553088568755101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 557138697035392379170067 835708045553088568755101)
    ·
      refine ⟨313390517082408213283163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 835708045553088568755101 313390517082408213283163)
      ·
        refine ⟨470085775623612319924745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313390517082408213283163 470085775623612319924745)
        ·
          refine ⟨352564331717709239943559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470085775623612319924745 352564331717709239943559)
          ·
            refine ⟨528846497576563859915339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352564331717709239943559 528846497576563859915339)
            ·
              refine ⟨793269746364845789873009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528846497576563859915339 793269746364845789873009)
              ·
                refine ⟨594952309773634342404757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793269746364845789873009 594952309773634342404757)
                ·
                  refine ⟨27888389520639109800223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 594952309773634342404757 27888389520639109800223)
                  ·
                    rfl

theorem cell22_244406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_244406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244406 prefixEnd_244406 := by exact prefixLift 244406
  have htrace : WordTrace (prefixWord ++ tailWord_244406) baseStart_244406 baseEnd_244406 := by
    simpa [prefixWord, tailWord_244406, baseEnd_244406] using wordTrace_append hprefix tailTrace_244406
  have hstable : (prefixWord ++ tailWord_244406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244406).length < 2 ^ (prefixWord ++ tailWord_244406).sum := by decide
  have hdescent : baseEnd_244406 < baseStart_244406 := by decide
  rcases family_descends (prefixWord ++ tailWord_244406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244449 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 3, 3]
def baseStart_244449 : Nat := 118140960795 + 244449 * 2 ^ 59
def prefixEnd_244449 : Nat := 4983230072969 + 3 ^ 40 * 244449 * 2
def baseEnd_244449 : Nat := 83679888340679550575537

theorem tailTrace_244449 : CollatzResearch.WordTrace tailWord_244449 prefixEnd_244449 83679888340679550575537 := by
  unfold tailWord_244449
  simp only [CollatzResearch.WordTrace]
  refine ⟨8915787491410496410536401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5943858327606997607024267 8915787491410496410536401)
  ·
    refine ⟨6686840618557872307902301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8915787491410496410536401 6686840618557872307902301)
    ·
      refine ⟨2507565231959202115463363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6686840618557872307902301 2507565231959202115463363)
      ·
        refine ⟨3761347847938803173195045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2507565231959202115463363 3761347847938803173195045)
        ·
          refine ⟨705252721488525594974071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3761347847938803173195045 705252721488525594974071)
          ·
            refine ⟨1057879082232788392461107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705252721488525594974071 1057879082232788392461107)
            ·
              refine ⟨1586818623349182588691661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057879082232788392461107 1586818623349182588691661)
              ·
                refine ⟨595056983755943470759373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1586818623349182588691661 595056983755943470759373)
                ·
                  refine ⟨223146368908478801534765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595056983755943470759373 223146368908478801534765)
                  ·
                    refine ⟨83679888340679550575537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 223146368908478801534765 83679888340679550575537)
                    ·
                      rfl

theorem cell22_244449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_244449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244449 prefixEnd_244449 := by exact prefixLift 244449
  have htrace : WordTrace (prefixWord ++ tailWord_244449) baseStart_244449 baseEnd_244449 := by
    simpa [prefixWord, tailWord_244449, baseEnd_244449] using wordTrace_append hprefix tailTrace_244449
  have hstable : (prefixWord ++ tailWord_244449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244449).length < 2 ^ (prefixWord ++ tailWord_244449).sum := by decide
  have hdescent : baseEnd_244449 < baseStart_244449 := by decide
  rcases family_descends (prefixWord ++ tailWord_244449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244492 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_244492 : Nat := 118140960795 + 244492 * 2 ^ 59
def prefixEnd_244492 : Nat := 4983230072969 + 3 ^ 40 * 244492 * 2
def baseEnd_244492 : Nat := 83694608119441771750405

theorem tailTrace_244492 : CollatzResearch.WordTrace tailWord_244492 prefixEnd_244492 83694608119441771750405 := by
  unfold tailWord_244492
  simp only [CollatzResearch.WordTrace]
  refine ⟨4458677915127357377175865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5944903886836476502901153 4458677915127357377175865)
  ·
    refine ⟨3344008436345518032881899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4458677915127357377175865 3344008436345518032881899)
    ·
      refine ⟨5016012654518277049322849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3344008436345518032881899 5016012654518277049322849)
      ·
        refine ⟨3762009490888707786992137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5016012654518277049322849 3762009490888707786992137)
        ·
          refine ⟨2821507118166530840244103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3762009490888707786992137 2821507118166530840244103)
          ·
            refine ⟨4232260677249796260366155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821507118166530840244103 4232260677249796260366155)
            ·
              refine ⟨6348391015874694390549233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4232260677249796260366155 6348391015874694390549233)
              ·
                refine ⟨4761293261906020792911925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6348391015874694390549233 4761293261906020792911925)
                ·
                  refine ⟨446371243303689449335493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4761293261906020792911925 446371243303689449335493)
                  ·
                    refine ⟨83694608119441771750405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 446371243303689449335493 83694608119441771750405)
                    ·
                      rfl

theorem cell22_244492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_244492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244492 prefixEnd_244492 := by exact prefixLift 244492
  have htrace : WordTrace (prefixWord ++ tailWord_244492) baseStart_244492 baseEnd_244492 := by
    simpa [prefixWord, tailWord_244492, baseEnd_244492] using wordTrace_append hprefix tailTrace_244492
  have hstable : (prefixWord ++ tailWord_244492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244492).length < 2 ^ (prefixWord ++ tailWord_244492).sum := by decide
  have hdescent : baseEnd_244492 < baseStart_244492 := by decide
  rcases family_descends (prefixWord ++ tailWord_244492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244526 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_244526 : Nat := 118140960795 + 244526 * 2 ^ 59
def prefixEnd_244526 : Nat := 4983230072969 + 3 ^ 40 * 244526 * 2
def baseEnd_244526 : Nat := 83706247014277016400301

theorem tailTrace_244526 : CollatzResearch.WordTrace tailWord_244526 prefixEnd_244526 83706247014277016400301 := by
  unfold tailWord_244526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1114824489016442320136179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5945730608087692374059621 1114824489016442320136179)
  ·
    refine ⟨1672236733524663480204269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1114824489016442320136179 1672236733524663480204269)
    ·
      refine ⟨627088775071748805076601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1672236733524663480204269 627088775071748805076601)
      ·
        refine ⟨470316581303811603807451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627088775071748805076601 470316581303811603807451)
        ·
          refine ⟨705474871955717405711177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470316581303811603807451 705474871955717405711177)
          ·
            refine ⟨529106153966788054283383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705474871955717405711177 529106153966788054283383)
            ·
              refine ⟨793659230950182081425075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529106153966788054283383 793659230950182081425075)
              ·
                refine ⟨1190488846425273122137613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793659230950182081425075 1190488846425273122137613)
                ·
                  refine ⟨446433317409477420801605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190488846425273122137613 446433317409477420801605)
                  ·
                    refine ⟨83706247014277016400301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 446433317409477420801605 83706247014277016400301)
                    ·
                      rfl

theorem cell22_244526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_244526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244526 prefixEnd_244526 := by exact prefixLift 244526
  have htrace : WordTrace (prefixWord ++ tailWord_244526) baseStart_244526 baseEnd_244526 := by
    simpa [prefixWord, tailWord_244526, baseEnd_244526] using wordTrace_append hprefix tailTrace_244526
  have hstable : (prefixWord ++ tailWord_244526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244526).length < 2 ^ (prefixWord ++ tailWord_244526).sum := by decide
  have hdescent : baseEnd_244526 < baseStart_244526 := by decide
  rcases family_descends (prefixWord ++ tailWord_244526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244556 : List Nat := [2, 2, 1, 3, 3, 1, 1, 4, 2, 3]
def baseStart_244556 : Nat := 118140960795 + 244556 * 2 ^ 59
def prefixEnd_244556 : Nat := 4983230072969 + 3 ^ 40 * 244556 * 2
def baseEnd_244556 : Nat := 83716516627366938150209

theorem tailTrace_244556 : CollatzResearch.WordTrace tailWord_244556 prefixEnd_244556 83716516627366938150209 := by
  unfold tailWord_244556
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459845051011426842340761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5946460068015235789787681 4459845051011426842340761)
  ·
    refine ⟨3344883788258570131755571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4459845051011426842340761 3344883788258570131755571)
    ·
      refine ⟨5017325682387855197633357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3344883788258570131755571 5017325682387855197633357)
      ·
        refine ⟨1881497130895445699112509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5017325682387855197633357 1881497130895445699112509)
        ·
          refine ⟨705561424085792137167191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1881497130895445699112509 705561424085792137167191)
          ·
            refine ⟨1058342136128688205750787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705561424085792137167191 1058342136128688205750787)
            ·
              refine ⟨1587513204193032308626181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058342136128688205750787 1587513204193032308626181)
              ·
                refine ⟨297658725786193557867409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1587513204193032308626181 297658725786193557867409)
                ·
                  refine ⟨223244044339645168400557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297658725786193557867409 223244044339645168400557)
                  ·
                    refine ⟨83716516627366938150209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 223244044339645168400557 83716516627366938150209)
                    ·
                      rfl

theorem cell22_244556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_244556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244556 prefixEnd_244556 := by exact prefixLift 244556
  have htrace : WordTrace (prefixWord ++ tailWord_244556) baseStart_244556 baseEnd_244556 := by
    simpa [prefixWord, tailWord_244556, baseEnd_244556] using wordTrace_append hprefix tailTrace_244556
  have hstable : (prefixWord ++ tailWord_244556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244556).length < 2 ^ (prefixWord ++ tailWord_244556).sum := by decide
  have hdescent : baseEnd_244556 < baseStart_244556 := by decide
  rcases family_descends (prefixWord ++ tailWord_244556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244569 : List Nat := [1, 2, 1, 2, 2, 6, 1, 7]
def baseStart_244569 : Nat := 118140960795 + 244569 * 2 ^ 59
def prefixEnd_244569 : Nat := 4983230072969 + 3 ^ 40 * 244569 * 2
def baseEnd_244569 : Nat := 9302329643671026397241

theorem tailTrace_244569 : CollatzResearch.WordTrace tailWord_244569 prefixEnd_244569 9302329643671026397241 := by
  unfold tailWord_244569
  simp only [CollatzResearch.WordTrace]
  refine ⟨8920164250975756904904761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5946776167317171269936507 8920164250975756904904761)
  ·
    refine ⟨6690123188231817678678571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8920164250975756904904761 6690123188231817678678571)
    ·
      refine ⟨10035184782347726518017857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6690123188231817678678571 10035184782347726518017857)
      ·
        refine ⟨7526388586760794888513393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10035184782347726518017857 7526388586760794888513393)
        ·
          refine ⟨5644791440070596166385045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7526388586760794888513393 5644791440070596166385045)
          ·
            refine ⟨264599598753309195299299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5644791440070596166385045 264599598753309195299299)
            ·
              refine ⟨396899398129963792948949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264599598753309195299299 396899398129963792948949)
              ·
                refine ⟨9302329643671026397241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 396899398129963792948949 9302329643671026397241)
                ·
                  rfl

theorem cell22_244569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 7].length) (baseStart_244569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244569 prefixEnd_244569 := by exact prefixLift 244569
  have htrace : WordTrace (prefixWord ++ tailWord_244569) baseStart_244569 baseEnd_244569 := by
    simpa [prefixWord, tailWord_244569, baseEnd_244569] using wordTrace_append hprefix tailTrace_244569
  have hstable : (prefixWord ++ tailWord_244569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244569).length < 2 ^ (prefixWord ++ tailWord_244569).sum := by decide
  have hdescent : baseEnd_244569 < baseStart_244569 := by decide
  rcases family_descends (prefixWord ++ tailWord_244569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244618 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 3, 3]
def baseStart_244618 : Nat := 118140960795 + 244618 * 2 ^ 59
def prefixEnd_244618 : Nat := 4983230072969 + 3 ^ 40 * 244618 * 2
def baseEnd_244618 : Nat := 83737740494419443100019

theorem tailTrace_244618 : CollatzResearch.WordTrace tailWord_244618 prefixEnd_244618 83737740494419443100019 := by
  unfold tailWord_244618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230487856949559568359627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5947967618532158848959005 2230487856949559568359627)
  ·
    refine ⟨3345731785424339352539441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2230487856949559568359627 3345731785424339352539441)
    ·
      refine ⟨2509298839068254514404581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3345731785424339352539441 2509298839068254514404581)
      ·
        refine ⟨470493532325297721450859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2509298839068254514404581 470493532325297721450859)
        ·
          refine ⟨705740298487946582176289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470493532325297721450859 705740298487946582176289)
          ·
            refine ⟨529305223865959936632217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705740298487946582176289 529305223865959936632217)
            ·
              refine ⟨396978917899469952474163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529305223865959936632217 396978917899469952474163)
              ·
                refine ⟨595468376849204928711245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396978917899469952474163 595468376849204928711245)
                ·
                  refine ⟨223300641318451848266717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595468376849204928711245 223300641318451848266717)
                  ·
                    refine ⟨83737740494419443100019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 223300641318451848266717 83737740494419443100019)
                    ·
                      rfl

theorem cell22_244618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_244618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244618 prefixEnd_244618 := by exact prefixLift 244618
  have htrace : WordTrace (prefixWord ++ tailWord_244618) baseStart_244618 baseEnd_244618 := by
    simpa [prefixWord, tailWord_244618, baseEnd_244618] using wordTrace_append hprefix tailTrace_244618
  have hstable : (prefixWord ++ tailWord_244618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244618).length < 2 ^ (prefixWord ++ tailWord_244618).sum := by decide
  have hdescent : baseEnd_244618 < baseStart_244618 := by decide
  rcases family_descends (prefixWord ++ tailWord_244618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244627 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 2, 8]
def baseStart_244627 : Nat := 118140960795 + 244627 * 2 ^ 59
def prefixEnd_244627 : Nat := 4983230072969 + 3 ^ 40 * 244627 * 2
def baseEnd_244627 : Nat := 83740821378346419624991

theorem tailTrace_244627 : CollatzResearch.WordTrace tailWord_244627 prefixEnd_244627 83740821378346419624991 := by
  unfold tailWord_244627
  simp only [CollatzResearch.WordTrace]
  refine ⟨8922279684765632810516135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5948186456510421873677423 8922279684765632810516135)
  ·
    refine ⟨13383419527148449215774203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8922279684765632810516135 13383419527148449215774203)
    ·
      refine ⟨20075129290722673823661305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13383419527148449215774203 20075129290722673823661305)
      ·
        refine ⟨15056346968042005367745979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20075129290722673823661305 15056346968042005367745979)
        ·
          refine ⟨22584520452063008051618969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15056346968042005367745979 22584520452063008051618969)
          ·
            refine ⟨16938390339047256038714227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22584520452063008051618969 16938390339047256038714227)
            ·
              refine ⟨25407585508570884058071341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16938390339047256038714227 25407585508570884058071341)
              ·
                refine ⟨9527844565714081521776753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25407585508570884058071341 9527844565714081521776753)
                ·
                  refine ⟨7145883424285561141332565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9527844565714081521776753 7145883424285561141332565)
                  ·
                    refine ⟨83740821378346419624991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7145883424285561141332565 83740821378346419624991)
                    ·
                      rfl

theorem cell22_244627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_244627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244627 prefixEnd_244627 := by exact prefixLift 244627
  have htrace : WordTrace (prefixWord ++ tailWord_244627) baseStart_244627 baseEnd_244627 := by
    simpa [prefixWord, tailWord_244627, baseEnd_244627] using wordTrace_append hprefix tailTrace_244627
  have hstable : (prefixWord ++ tailWord_244627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244627).length < 2 ^ (prefixWord ++ tailWord_244627).sum := by decide
  have hdescent : baseEnd_244627 < baseStart_244627 := by decide
  rcases family_descends (prefixWord ++ tailWord_244627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244629 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_244629 : Nat := 118140960795 + 244629 * 2 ^ 59
def prefixEnd_244629 : Nat := 4983230072969 + 3 ^ 40 * 244629 * 2
def baseEnd_244629 : Nat := 83741506019219081074985

theorem tailTrace_244629 : CollatzResearch.WordTrace tailWord_244629 prefixEnd_244629 83741506019219081074985 := by
  unfold tailWord_244629
  simp only [CollatzResearch.WordTrace]
  refine ⟨8922352630758387152088941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5948235087172258101392627 8922352630758387152088941)
  ·
    refine ⟨3345882236534395182033353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8922352630758387152088941 3345882236534395182033353)
    ·
      refine ⟨2509411677400796386525015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3345882236534395182033353 2509411677400796386525015)
      ·
        refine ⟨3764117516101194579787523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2509411677400796386525015 3764117516101194579787523)
        ·
          refine ⟨5646176274151791869681285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3764117516101194579787523 5646176274151791869681285)
          ·
            refine ⟨1058658051403460975565241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5646176274151791869681285 1058658051403460975565241)
            ·
              refine ⟨793993538552595731673931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058658051403460975565241 793993538552595731673931)
              ·
                refine ⟨1190990307828893597510897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793993538552595731673931 1190990307828893597510897)
                ·
                  refine ⟨893242730871670198133173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1190990307828893597510897 893242730871670198133173)
                  ·
                    refine ⟨83741506019219081074985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 893242730871670198133173 83741506019219081074985)
                    ·
                      rfl

theorem cell22_244629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_244629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244629 prefixEnd_244629 := by exact prefixLift 244629
  have htrace : WordTrace (prefixWord ++ tailWord_244629) baseStart_244629 baseEnd_244629 := by
    simpa [prefixWord, tailWord_244629, baseEnd_244629] using wordTrace_append hprefix tailTrace_244629
  have hstable : (prefixWord ++ tailWord_244629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244629).length < 2 ^ (prefixWord ++ tailWord_244629).sum := by decide
  have hdescent : baseEnd_244629 < baseStart_244629 := by decide
  rcases family_descends (prefixWord ++ tailWord_244629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244631 : List Nat := [1, 1, 3, 3, 1, 2, 5, 1, 5]
def baseStart_244631 : Nat := 118140960795 + 244631 * 2 ^ 59
def prefixEnd_244631 : Nat := 4983230072969 + 3 ^ 40 * 244631 * 2
def baseEnd_244631 : Nat := 27914063553363914174993

theorem tailTrace_244631 : CollatzResearch.WordTrace tailWord_244631 prefixEnd_244631 27914063553363914174993 := by
  unfold tailWord_244631
  simp only [CollatzResearch.WordTrace]
  refine ⟨8922425576751141493661747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5948283717834094329107831 8922425576751141493661747)
  ·
    refine ⟨13383638365126712240492621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8922425576751141493661747 13383638365126712240492621)
    ·
      refine ⟨5018864386922517090184733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13383638365126712240492621 5018864386922517090184733)
      ·
        refine ⟨1882074145095943908819275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5018864386922517090184733 1882074145095943908819275)
        ·
          refine ⟨2823111217643915863228913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1882074145095943908819275 2823111217643915863228913)
          ·
            refine ⟨2117333413232936897421685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2823111217643915863228913 2117333413232936897421685)
            ·
              refine ⟨198500007490587834133283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2117333413232936897421685 198500007490587834133283)
              ·
                refine ⟨297750011235881751199925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198500007490587834133283 297750011235881751199925)
                ·
                  refine ⟨27914063553363914174993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 297750011235881751199925 27914063553363914174993)
                  ·
                    rfl

theorem cell22_244631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 5].length) (baseStart_244631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244631 prefixEnd_244631 := by exact prefixLift 244631
  have htrace : WordTrace (prefixWord ++ tailWord_244631) baseStart_244631 baseEnd_244631 := by
    simpa [prefixWord, tailWord_244631, baseEnd_244631] using wordTrace_append hprefix tailTrace_244631
  have hstable : (prefixWord ++ tailWord_244631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244631).length < 2 ^ (prefixWord ++ tailWord_244631).sum := by decide
  have hdescent : baseEnd_244631 < baseStart_244631 := by decide
  rcases family_descends (prefixWord ++ tailWord_244631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244661 : List Nat := [1, 3, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_244661 : Nat := 118140960795 + 244661 * 2 ^ 59
def prefixEnd_244661 : Nat := 4983230072969 + 3 ^ 40 * 244661 * 2
def baseEnd_244661 : Nat := 83752460273181664274887

theorem tailTrace_244661 : CollatzResearch.WordTrace tailWord_244661 prefixEnd_244661 83752460273181664274887 := by
  unfold tailWord_244661
  simp only [CollatzResearch.WordTrace]
  refine ⟨8923519766642456617253837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5949013177761637744835891 8923519766642456617253837)
  ·
    refine ⟨3346319912490921231470189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8923519766642456617253837 3346319912490921231470189)
    ·
      refine ⟨1254869967184095461801321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3346319912490921231470189 1254869967184095461801321)
      ·
        refine ⟨941152475388071596350991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1254869967184095461801321 941152475388071596350991)
        ·
          refine ⟨1411728713082107394526487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941152475388071596350991 1411728713082107394526487)
          ·
            refine ⟨2117593069623161091789731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411728713082107394526487 2117593069623161091789731)
            ·
              refine ⟨3176389604434741637684597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117593069623161091789731 3176389604434741637684597)
              ·
                refine ⟨297786525415757028532931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3176389604434741637684597 297786525415757028532931)
                ·
                  refine ⟨446679788123635542799397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297786525415757028532931 446679788123635542799397)
                  ·
                    refine ⟨83752460273181664274887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 446679788123635542799397 83752460273181664274887)
                    ·
                      rfl

theorem cell22_244661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_244661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244661 prefixEnd_244661 := by exact prefixLift 244661
  have htrace : WordTrace (prefixWord ++ tailWord_244661) baseStart_244661 baseEnd_244661 := by
    simpa [prefixWord, tailWord_244661, baseEnd_244661] using wordTrace_append hprefix tailTrace_244661
  have hstable : (prefixWord ++ tailWord_244661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244661).length < 2 ^ (prefixWord ++ tailWord_244661).sum := by decide
  have hdescent : baseEnd_244661 < baseStart_244661 := by decide
  rcases family_descends (prefixWord ++ tailWord_244661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244689 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 4, 4]
def baseStart_244689 : Nat := 118140960795 + 244689 * 2 ^ 59
def prefixEnd_244689 : Nat := 4983230072969 + 3 ^ 40 * 244689 * 2
def baseEnd_244689 : Nat := 83762045245398924574801

theorem tailTrace_244689 : CollatzResearch.WordTrace tailWord_244689 prefixEnd_244689 83762045245398924574801 := by
  unfold tailWord_244689
  simp only [CollatzResearch.WordTrace]
  refine ⟨8924541010541017399273121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5949694007027344932848747 8924541010541017399273121)
  ·
    refine ⟨6693405757905763049454841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8924541010541017399273121 6693405757905763049454841)
    ·
      refine ⟨5020054318429322287091131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6693405757905763049454841 5020054318429322287091131)
      ·
        refine ⟨7530081477643983430636697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5020054318429322287091131 7530081477643983430636697)
        ·
          refine ⟨5647561108232987572977523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7530081477643983430636697 5647561108232987572977523)
          ·
            refine ⟨8471341662349481359466285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5647561108232987572977523 8471341662349481359466285)
            ·
              refine ⟨3176753123381055509799857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8471341662349481359466285 3176753123381055509799857)
              ·
                refine ⟨2382564842535791632349893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3176753123381055509799857 2382564842535791632349893)
                ·
                  refine ⟨446730907975460931065605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2382564842535791632349893 446730907975460931065605)
                  ·
                    refine ⟨83762045245398924574801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 446730907975460931065605 83762045245398924574801)
                    ·
                      rfl

theorem cell22_244689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_244689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244689 prefixEnd_244689 := by exact prefixLift 244689
  have htrace : WordTrace (prefixWord ++ tailWord_244689) baseStart_244689 baseEnd_244689 := by
    simpa [prefixWord, tailWord_244689, baseEnd_244689] using wordTrace_append hprefix tailTrace_244689
  have hstable : (prefixWord ++ tailWord_244689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244689).length < 2 ^ (prefixWord ++ tailWord_244689).sum := by decide
  have hdescent : baseEnd_244689 < baseStart_244689 := by decide
  rcases family_descends (prefixWord ++ tailWord_244689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244770 : List Nat := [3, 3, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_244770 : Nat := 118140960795 + 244770 * 2 ^ 59
def prefixEnd_244770 : Nat := 4983230072969 + 3 ^ 40 * 244770 * 2
def baseEnd_244770 : Nat := 83789773200741713299553

theorem tailTrace_244770 : CollatzResearch.WordTrace tailWord_244770 prefixEnd_244770 83789773200741713299553 := by
  unfold tailWord_244770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2231873830811892058242941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5951663548831712155314509 2231873830811892058242941)
  ·
    refine ⟨836952686554459521841103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2231873830811892058242941 836952686554459521841103)
    ·
      refine ⟨1255429029831689282761655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 836952686554459521841103 1255429029831689282761655)
      ·
        refine ⟨1883143544747533924142483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255429029831689282761655 1883143544747533924142483)
        ·
          refine ⟨2824715317121300886213725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883143544747533924142483 2824715317121300886213725)
          ·
            refine ⟨1059268243920487832330147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2824715317121300886213725 1059268243920487832330147)
            ·
              refine ⟨1588902365880731748495221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059268243920487832330147 1588902365880731748495221)
              ·
                refine ⟨148959596801318601421427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1588902365880731748495221 148959596801318601421427)
                ·
                  refine ⟨223439395201977902132141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148959596801318601421427 223439395201977902132141)
                  ·
                    refine ⟨83789773200741713299553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 223439395201977902132141 83789773200741713299553)
                    ·
                      rfl

theorem cell22_244770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_244770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244770 prefixEnd_244770 := by exact prefixLift 244770
  have htrace : WordTrace (prefixWord ++ tailWord_244770) baseStart_244770 baseEnd_244770 := by
    simpa [prefixWord, tailWord_244770, baseEnd_244770] using wordTrace_append hprefix tailTrace_244770
  have hstable : (prefixWord ++ tailWord_244770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244770).length < 2 ^ (prefixWord ++ tailWord_244770).sum := by decide
  have hdescent : baseEnd_244770 < baseStart_244770 := by decide
  rcases family_descends (prefixWord ++ tailWord_244770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244798 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_244798 : Nat := 118140960795 + 244798 * 2 ^ 59
def prefixEnd_244798 : Nat := 4983230072969 + 3 ^ 40 * 244798 * 2
def baseEnd_244798 : Nat := 83799358172958973599467

theorem tailTrace_244798 : CollatzResearch.WordTrace tailWord_244798 prefixEnd_244798 83799358172958973599467 := by
  unfold tailWord_244798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1116064570893266126873881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5952344378097419343327365 1116064570893266126873881)
  ·
    refine ⟨837048428169949595155411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1116064570893266126873881 837048428169949595155411)
    ·
      refine ⟨1255572642254924392733117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837048428169949595155411 1255572642254924392733117)
      ·
        refine ⟨470839740845596647274919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1255572642254924392733117 470839740845596647274919)
        ·
          refine ⟨706259611268394970912379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470839740845596647274919 706259611268394970912379)
          ·
            refine ⟨1059389416902592456368569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706259611268394970912379 1059389416902592456368569)
            ·
              refine ⟨794542062676944342276427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059389416902592456368569 794542062676944342276427)
              ·
                refine ⟨1191813094015416513414641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794542062676944342276427 1191813094015416513414641)
                ·
                  refine ⟨893859820511562385060981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1191813094015416513414641 893859820511562385060981)
                  ·
                    refine ⟨83799358172958973599467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 893859820511562385060981 83799358172958973599467)
                    ·
                      rfl

theorem cell22_244798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_244798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244798 prefixEnd_244798 := by exact prefixLift 244798
  have htrace : WordTrace (prefixWord ++ tailWord_244798) baseStart_244798 baseEnd_244798 := by
    simpa [prefixWord, tailWord_244798, baseEnd_244798] using wordTrace_append hprefix tailTrace_244798
  have hstable : (prefixWord ++ tailWord_244798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244798).length < 2 ^ (prefixWord ++ tailWord_244798).sum := by decide
  have hdescent : baseEnd_244798 < baseStart_244798 := by decide
  rcases family_descends (prefixWord ++ tailWord_244798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244841 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 4, 4]
def baseStart_244841 : Nat := 118140960795 + 244841 * 2 ^ 59
def prefixEnd_244841 : Nat := 4983230072969 + 3 ^ 40 * 244841 * 2
def baseEnd_244841 : Nat := 83814077951721194774335

theorem tailTrace_244841 : CollatzResearch.WordTrace tailWord_244841 prefixEnd_244841 83814077951721194774335 := by
  unfold tailWord_244841
  simp only [CollatzResearch.WordTrace]
  refine ⟨8930084905990347358806377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5953389937326898239204251 8930084905990347358806377)
  ·
    refine ⟨6697563679492760519104783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8930084905990347358806377 6697563679492760519104783)
    ·
      refine ⟨10046345519239140778657175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6697563679492760519104783 10046345519239140778657175)
      ·
        refine ⟨15069518278858711167985763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10046345519239140778657175 15069518278858711167985763)
        ·
          refine ⟨22604277418288066751978645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15069518278858711167985763 22604277418288066751978645)
          ·
            refine ⟨1059575503982253128998999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22604277418288066751978645 1059575503982253128998999)
            ·
              refine ⟨1589363255973379693498499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059575503982253128998999 1589363255973379693498499)
              ·
                refine ⟨2384044883960069540247749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589363255973379693498499 2384044883960069540247749)
                ·
                  refine ⟨447008415742513038796453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2384044883960069540247749 447008415742513038796453)
                  ·
                    refine ⟨83814077951721194774335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 447008415742513038796453 83814077951721194774335)
                    ·
                      rfl

theorem cell22_244841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_244841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244841 prefixEnd_244841 := by exact prefixLift 244841
  have htrace : WordTrace (prefixWord ++ tailWord_244841) baseStart_244841 baseEnd_244841 := by
    simpa [prefixWord, tailWord_244841, baseEnd_244841] using wordTrace_append hprefix tailTrace_244841
  have hstable : (prefixWord ++ tailWord_244841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244841).length < 2 ^ (prefixWord ++ tailWord_244841).sum := by decide
  have hdescent : baseEnd_244841 < baseStart_244841 := by decide
  rcases family_descends (prefixWord ++ tailWord_244841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244903 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 2, 6]
def baseStart_244903 : Nat := 118140960795 + 244903 * 2 ^ 59
def prefixEnd_244903 : Nat := 4983230072969 + 3 ^ 40 * 244903 * 2
def baseEnd_244903 : Nat := 83835301818773699724145

theorem tailTrace_244903 : CollatzResearch.WordTrace tailWord_244903 prefixEnd_244903 83835301818773699724145 := by
  unfold tailWord_244903
  simp only [CollatzResearch.WordTrace]
  refine ⟨8932346231765731947563363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5954897487843821298375575 8932346231765731947563363)
  ·
    refine ⟨13398519347648597921345045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8932346231765731947563363 13398519347648597921345045)
    ·
      refine ⟨628055594421028027563049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13398519347648597921345045 628055594421028027563049)
      ·
        refine ⟨471041695815771020672287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628055594421028027563049 471041695815771020672287)
        ·
          refine ⟨706562543723656531008431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471041695815771020672287 706562543723656531008431)
          ·
            refine ⟨1059843815585484796512647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706562543723656531008431 1059843815585484796512647)
            ·
              refine ⟨1589765723378227194768971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059843815585484796512647 1589765723378227194768971)
              ·
                refine ⟨2384648585067340792153457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589765723378227194768971 2384648585067340792153457)
                ·
                  refine ⟨1788486438800505594115093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2384648585067340792153457 1788486438800505594115093)
                  ·
                    refine ⟨83835301818773699724145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1788486438800505594115093 83835301818773699724145)
                    ·
                      rfl

theorem cell22_244903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_244903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244903 prefixEnd_244903 := by exact prefixLift 244903
  have htrace : WordTrace (prefixWord ++ tailWord_244903) baseStart_244903 baseEnd_244903 := by
    simpa [prefixWord, tailWord_244903, baseEnd_244903] using wordTrace_append hprefix tailTrace_244903
  have hstable : (prefixWord ++ tailWord_244903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244903).length < 2 ^ (prefixWord ++ tailWord_244903).sum := by decide
  have hdescent : baseEnd_244903 < baseStart_244903 := by decide
  rcases family_descends (prefixWord ++ tailWord_244903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244952 : List Nat := [2, 1, 2, 2, 6, 1, 1, 2, 5]
def baseStart_244952 : Nat := 118140960795 + 244952 * 2 ^ 59
def prefixEnd_244952 : Nat := 4983230072969 + 3 ^ 40 * 244952 * 2
def baseEnd_244952 : Nat := 27950691840051301749665

theorem tailTrace_244952 : CollatzResearch.WordTrace tailWord_244952 prefixEnd_244952 27950691840051301749665 := by
  unfold tailWord_244952
  simp only [CollatzResearch.WordTrace]
  refine ⟨4467066704294106658048555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5956088939058808877398073 4467066704294106658048555)
  ·
    refine ⟨6700600056441159987072833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4467066704294106658048555 6700600056441159987072833)
    ·
      refine ⟨5025450042330869990304625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6700600056441159987072833 5025450042330869990304625)
      ·
        refine ⟨3769087531748152492728469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5025450042330869990304625 3769087531748152492728469)
        ·
          refine ⟨176675978050694648096647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3769087531748152492728469 176675978050694648096647)
          ·
            refine ⟨265013967076041972144971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176675978050694648096647 265013967076041972144971)
            ·
              refine ⟨397520950614062958217457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265013967076041972144971 397520950614062958217457)
              ·
                refine ⟨298140712960547218663093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397520950614062958217457 298140712960547218663093)
                ·
                  refine ⟨27950691840051301749665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 298140712960547218663093 27950691840051301749665)
                  ·
                    rfl

theorem cell22_244952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 5].length) (baseStart_244952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244952 prefixEnd_244952 := by exact prefixLift 244952
  have htrace : WordTrace (prefixWord ++ tailWord_244952) baseStart_244952 baseEnd_244952 := by
    simpa [prefixWord, tailWord_244952, baseEnd_244952] using wordTrace_append hprefix tailTrace_244952
  have hstable : (prefixWord ++ tailWord_244952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244952).length < 2 ^ (prefixWord ++ tailWord_244952).sum := by decide
  have hdescent : baseEnd_244952 < baseStart_244952 := by decide
  rcases family_descends (prefixWord ++ tailWord_244952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244993 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 1, 6]
def baseStart_244993 : Nat := 118140960795 + 244993 * 2 ^ 59
def prefixEnd_244993 : Nat := 4983230072969 + 3 ^ 40 * 244993 * 2
def baseEnd_244993 : Nat := 83866110658043464973869

theorem tailTrace_244993 : CollatzResearch.WordTrace tailWord_244993 prefixEnd_244993 83866110658043464973869 := by
  unfold tailWord_244993
  simp only [CollatzResearch.WordTrace]
  refine ⟨8935628801439677318339633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5957085867626451545559755 8935628801439677318339633)
  ·
    refine ⟨6701721601079757988754725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8935628801439677318339633 6701721601079757988754725)
    ·
      refine ⟨1256572800202454622891511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6701721601079757988754725 1256572800202454622891511)
      ·
        refine ⟨1884859200303681934337267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256572800202454622891511 1884859200303681934337267)
        ·
          refine ⟨2827288800455522901505901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884859200303681934337267 2827288800455522901505901)
          ·
            refine ⟨1060233300170821088064713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2827288800455522901505901 1060233300170821088064713)
            ·
              refine ⟨795174975128115816048535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060233300170821088064713 795174975128115816048535)
              ·
                refine ⟨1192762462692173724072803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795174975128115816048535 1192762462692173724072803)
                ·
                  refine ⟨1789143694038260586109205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192762462692173724072803 1789143694038260586109205)
                  ·
                    refine ⟨83866110658043464973869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1789143694038260586109205 83866110658043464973869)
                    ·
                      rfl

theorem cell22_244993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_244993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_244993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_244993 prefixEnd_244993 := by exact prefixLift 244993
  have htrace : WordTrace (prefixWord ++ tailWord_244993) baseStart_244993 baseEnd_244993 := by
    simpa [prefixWord, tailWord_244993, baseEnd_244993] using wordTrace_append hprefix tailTrace_244993
  have hstable : (prefixWord ++ tailWord_244993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244993).length < 2 ^ (prefixWord ++ tailWord_244993).sum := by decide
  have hdescent : baseEnd_244993 < baseStart_244993 := by decide
  rcases family_descends (prefixWord ++ tailWord_244993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245029 : List Nat := [1, 3, 1, 2, 4, 3, 2, 1, 2, 3]
def baseStart_245029 : Nat := 118140960795 + 245029 * 2 ^ 59
def prefixEnd_245029 : Nat := 4983230072969 + 3 ^ 40 * 245029 * 2
def baseEnd_245029 : Nat := 83878434193751371073759

theorem tailTrace_245029 : CollatzResearch.WordTrace tailWord_245029 prefixEnd_245029 83878434193751371073759 := by
  unfold tailWord_245029
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936941829309255466650141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5957961219539503644433427 8936941829309255466650141)
  ·
    refine ⟨3351353185990970799993803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8936941829309255466650141 3351353185990970799993803)
    ·
      refine ⟨5027029778986456199990705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3351353185990970799993803 5027029778986456199990705)
      ·
        refine ⟨3770272334239842149993029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5027029778986456199990705 3770272334239842149993029)
        ·
          refine ⟨706926062669970403123693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3770272334239842149993029 706926062669970403123693)
          ·
            refine ⟨265097273501238901171385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 706926062669970403123693 265097273501238901171385)
            ·
              refine ⟨198822955125929175878539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265097273501238901171385 198822955125929175878539)
              ·
                refine ⟨298234432688893763817809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198822955125929175878539 298234432688893763817809)
                ·
                  refine ⟨223675824516670322863357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298234432688893763817809 223675824516670322863357)
                  ·
                    refine ⟨83878434193751371073759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 223675824516670322863357 83878434193751371073759)
                    ·
                      rfl

theorem cell22_245029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_245029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245029 prefixEnd_245029 := by exact prefixLift 245029
  have htrace : WordTrace (prefixWord ++ tailWord_245029) baseStart_245029 baseEnd_245029 := by
    simpa [prefixWord, tailWord_245029, baseEnd_245029] using wordTrace_append hprefix tailTrace_245029
  have hstable : (prefixWord ++ tailWord_245029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245029).length < 2 ^ (prefixWord ++ tailWord_245029).sum := by decide
  have hdescent : baseEnd_245029 < baseStart_245029 := by decide
  rcases family_descends (prefixWord ++ tailWord_245029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245070 : List Nat := [4, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_245070 : Nat := 118140960795 + 245070 * 2 ^ 59
def prefixEnd_245070 : Nat := 4983230072969 + 3 ^ 40 * 245070 * 2
def baseEnd_245070 : Nat := 27964156443880310266211

theorem tailTrace_245070 : CollatzResearch.WordTrace tailWord_245070 prefixEnd_245070 27964156443880310266211 := by
  unfold tailWord_245070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117304652770089933611583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5958958148107146312595109 1117304652770089933611583)
  ·
    refine ⟨1675956979155134900417375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1117304652770089933611583 1675956979155134900417375)
    ·
      refine ⟨2513935468732702350626063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1675956979155134900417375 2513935468732702350626063)
      ·
        refine ⟨3770903203099053525939095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2513935468732702350626063 3770903203099053525939095)
        ·
          refine ⟨5656354804648580288908643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3770903203099053525939095 5656354804648580288908643)
          ·
            refine ⟨8484532206972870433362965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5656354804648580288908643 8484532206972870433362965)
            ·
              refine ⟨397712447201853301563889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8484532206972870433362965 397712447201853301563889)
              ·
                refine ⟨298284335401389976172917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397712447201853301563889 298284335401389976172917)
                ·
                  refine ⟨27964156443880310266211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 298284335401389976172917 27964156443880310266211)
                  ·
                    rfl

theorem cell22_245070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_245070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245070 prefixEnd_245070 := by exact prefixLift 245070
  have htrace : WordTrace (prefixWord ++ tailWord_245070) baseStart_245070 baseEnd_245070 := by
    simpa [prefixWord, tailWord_245070, baseEnd_245070] using wordTrace_append hprefix tailTrace_245070
  have hstable : (prefixWord ++ tailWord_245070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245070).length < 2 ^ (prefixWord ++ tailWord_245070).sum := by decide
  have hdescent : baseEnd_245070 < baseStart_245070 := by decide
  rcases family_descends (prefixWord ++ tailWord_245070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245100 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_245100 : Nat := 118140960795 + 245100 * 2 ^ 59
def prefixEnd_245100 : Nat := 4983230072969 + 3 ^ 40 * 245100 * 2
def baseEnd_245100 : Nat := 83902738944730852548541

theorem tailTrace_245100 : CollatzResearch.WordTrace tailWord_245100 prefixEnd_245100 83902738944730852548541 := by
  unfold tailWord_245100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4469765706026017296242377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5959687608034689728323169 4469765706026017296242377)
  ·
    refine ⟨3352324279519512972181783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4469765706026017296242377 3352324279519512972181783)
    ·
      refine ⟨5028486419279269458272675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3352324279519512972181783 5028486419279269458272675)
      ·
        refine ⟨7542729628918904187409013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5028486419279269458272675 7542729628918904187409013)
        ·
          refine ⟨707130902711147267569595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7542729628918904187409013 707130902711147267569595)
          ·
            refine ⟨1060696354066720901354393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707130902711147267569595 1060696354066720901354393)
            ·
              refine ⟨795522265550040676015795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060696354066720901354393 795522265550040676015795)
              ·
                refine ⟨1193283398325061014023693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795522265550040676015795 1193283398325061014023693)
                ·
                  refine ⟨447481274371897880258885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193283398325061014023693 447481274371897880258885)
                  ·
                    refine ⟨83902738944730852548541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 447481274371897880258885 83902738944730852548541)
                    ·
                      rfl

theorem cell22_245100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_245100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245100 prefixEnd_245100 := by exact prefixLift 245100
  have htrace : WordTrace (prefixWord ++ tailWord_245100) baseStart_245100 baseEnd_245100 := by
    simpa [prefixWord, tailWord_245100, baseEnd_245100] using wordTrace_append hprefix tailTrace_245100
  have hstable : (prefixWord ++ tailWord_245100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245100).length < 2 ^ (prefixWord ++ tailWord_245100).sum := by decide
  have hdescent : baseEnd_245100 < baseStart_245100 := by decide
  rcases family_descends (prefixWord ++ tailWord_245100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245143 : List Nat := [1, 1, 3, 3, 1, 1, 1, 11]
def baseStart_245143 : Nat := 118140960795 + 245143 * 2 ^ 59
def prefixEnd_245143 : Nat := 4983230072969 + 3 ^ 40 * 245143 * 2
def baseEnd_245143 : Nat := 9324162080388119302601

theorem tailTrace_245143 : CollatzResearch.WordTrace tailWord_245143 prefixEnd_245143 9324162080388119302601 := by
  unfold tailWord_245143
  simp only [CollatzResearch.WordTrace]
  refine ⟨8941099750896252936300083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5960733167264168624200055 8941099750896252936300083)
  ·
    refine ⟨13411649626344379404450125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8941099750896252936300083 13411649626344379404450125)
    ·
      refine ⟨5029368609879142276668797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13411649626344379404450125 5029368609879142276668797)
      ·
        refine ⟨1886013228704678353750799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5029368609879142276668797 1886013228704678353750799)
        ·
          refine ⟨2829019843057017530626199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886013228704678353750799 2829019843057017530626199)
          ·
            refine ⟨4243529764585526295939299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829019843057017530626199 4243529764585526295939299)
            ·
              refine ⟨6365294646878289443908949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243529764585526295939299 6365294646878289443908949)
              ·
                refine ⟨9324162080388119302601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 6365294646878289443908949 9324162080388119302601)
                ·
                  rfl

theorem cell22_245143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 11].length) (baseStart_245143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245143 prefixEnd_245143 := by exact prefixLift 245143
  have htrace : WordTrace (prefixWord ++ tailWord_245143) baseStart_245143 baseEnd_245143 := by
    simpa [prefixWord, tailWord_245143, baseEnd_245143] using wordTrace_append hprefix tailTrace_245143
  have hstable : (prefixWord ++ tailWord_245143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245143).length < 2 ^ (prefixWord ++ tailWord_245143).sum := by decide
  have hdescent : baseEnd_245143 < baseStart_245143 := by decide
  rcases family_descends (prefixWord ++ tailWord_245143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245177 : List Nat := [1, 2, 1, 4, 5, 1, 8]
def baseStart_245177 : Nat := 118140960795 + 245177 * 2 ^ 59
def prefixEnd_245177 : Nat := 4983230072969 + 3 ^ 40 * 245177 * 2
def baseEnd_245177 : Nat := 3108485096975122902715

theorem tailTrace_245177 : CollatzResearch.WordTrace tailWord_245177 prefixEnd_245177 3108485096975122902715 := by
  unfold tailWord_245177
  simp only [CollatzResearch.WordTrace]
  refine ⟨8942339832773076743037785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5961559888515384495358523 8942339832773076743037785)
  ·
    refine ⟨6706754874579807557278339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8942339832773076743037785 6706754874579807557278339)
    ·
      refine ⟨10060132311869711335917509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6706754874579807557278339 10060132311869711335917509)
      ·
        refine ⟨1886274808475570875484533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10060132311869711335917509 1886274808475570875484533)
        ·
          refine ⟨176838263294584769576675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1886274808475570875484533 176838263294584769576675)
          ·
            refine ⟨265257394941877154365013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176838263294584769576675 265257394941877154365013)
            ·
              refine ⟨3108485096975122902715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 265257394941877154365013 3108485096975122902715)
              ·
                rfl

theorem cell22_245177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 8].length) (baseStart_245177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245177 prefixEnd_245177 := by exact prefixLift 245177
  have htrace : WordTrace (prefixWord ++ tailWord_245177) baseStart_245177 baseEnd_245177 := by
    simpa [prefixWord, tailWord_245177, baseEnd_245177] using wordTrace_append hprefix tailTrace_245177
  have hstable : (prefixWord ++ tailWord_245177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245177).length < 2 ^ (prefixWord ++ tailWord_245177).sum := by decide
  have hdescent : baseEnd_245177 < baseStart_245177 := by decide
  rcases family_descends (prefixWord ++ tailWord_245177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245282 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_245282 : Nat := 118140960795 + 245282 * 2 ^ 59
def prefixEnd_245282 : Nat := 4983230072969 + 3 ^ 40 * 245282 * 2
def baseEnd_245282 : Nat := 83965041264143044497983

theorem tailTrace_245282 : CollatzResearch.WordTrace tailWord_245282 prefixEnd_245282 83965041264143044497983 := by
  unfold tailWord_245282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2236542374348169918902525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5964112998261786450406733 2236542374348169918902525)
  ·
    refine ⟨838703390380563719588447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2236542374348169918902525 838703390380563719588447)
    ·
      refine ⟨1258055085570845579382671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838703390380563719588447 1258055085570845579382671)
      ·
        refine ⟨1887082628356268369074007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1258055085570845579382671 1887082628356268369074007)
        ·
          refine ⟨2830623942534402553611011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887082628356268369074007 2830623942534402553611011)
          ·
            refine ⟨4245935913801603830416517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830623942534402553611011 4245935913801603830416517)
            ·
              refine ⟨796112983837800718203097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4245935913801603830416517 796112983837800718203097)
              ·
                refine ⟨597084737878350538652323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796112983837800718203097 597084737878350538652323)
                ·
                  refine ⟨895627106817525807978485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597084737878350538652323 895627106817525807978485)
                  ·
                    refine ⟨83965041264143044497983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 895627106817525807978485 83965041264143044497983)
                    ·
                      rfl

theorem cell22_245282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_245282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245282 prefixEnd_245282 := by exact prefixLift 245282
  have htrace : WordTrace (prefixWord ++ tailWord_245282) baseStart_245282 baseEnd_245282 := by
    simpa [prefixWord, tailWord_245282, baseEnd_245282] using wordTrace_append hprefix tailTrace_245282
  have hstable : (prefixWord ++ tailWord_245282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245282).length < 2 ^ (prefixWord ++ tailWord_245282).sum := by decide
  have hdescent : baseEnd_245282 < baseStart_245282 := by decide
  rcases family_descends (prefixWord ++ tailWord_245282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245299 : List Nat := [1, 1, 1, 2, 4, 3, 3, 2, 2, 3]
def baseStart_245299 : Nat := 118140960795 + 245299 * 2 ^ 59
def prefixEnd_245299 : Nat := 4983230072969 + 3 ^ 40 * 245299 * 2
def baseEnd_245299 : Nat := 83970860711560666822931

theorem tailTrace_245299 : CollatzResearch.WordTrace tailWord_245299 prefixEnd_245299 83970860711560666822931 := by
  unfold tailWord_245299
  simp only [CollatzResearch.WordTrace]
  refine ⟨8946789538331091578978951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5964526358887394385985967 8946789538331091578978951)
  ·
    refine ⟨13420184307496637368468427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8946789538331091578978951 13420184307496637368468427)
    ·
      refine ⟨20130276461244956052702641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13420184307496637368468427 20130276461244956052702641)
      ·
        refine ⟨15097707345933717039526981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20130276461244956052702641 15097707345933717039526981)
        ·
          refine ⟨2830820127362571944911309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15097707345933717039526981 2830820127362571944911309)
          ·
            refine ⟨1061557547760964479341741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2830820127362571944911309 1061557547760964479341741)
            ·
              refine ⟨398084080410361679753153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1061557547760964479341741 398084080410361679753153)
              ·
                refine ⟨298563060307771259814865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398084080410361679753153 298563060307771259814865)
                ·
                  refine ⟨223922295230828444861149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298563060307771259814865 223922295230828444861149)
                  ·
                    refine ⟨83970860711560666822931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 223922295230828444861149 83970860711560666822931)
                    ·
                      rfl

theorem cell22_245299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 3].length) (baseStart_245299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245299 prefixEnd_245299 := by exact prefixLift 245299
  have htrace : WordTrace (prefixWord ++ tailWord_245299) baseStart_245299 baseEnd_245299 := by
    simpa [prefixWord, tailWord_245299, baseEnd_245299] using wordTrace_append hprefix tailTrace_245299
  have hstable : (prefixWord ++ tailWord_245299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245299).length < 2 ^ (prefixWord ++ tailWord_245299).sum := by decide
  have hdescent : baseEnd_245299 < baseStart_245299 := by decide
  rcases family_descends (prefixWord ++ tailWord_245299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245387 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 3, 4]
def baseStart_245387 : Nat := 118140960795 + 245387 * 2 ^ 59
def prefixEnd_245387 : Nat := 4983230072969 + 3 ^ 40 * 245387 * 2
def baseEnd_245387 : Nat := 84000984909957770622661

theorem tailTrace_245387 : CollatzResearch.WordTrace tailWord_245387 prefixEnd_245387 84000984909957770622661 := by
  unfold tailWord_245387
  simp only [CollatzResearch.WordTrace]
  refine ⟨8949999162012282608182415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5966666108008188405454943 8949999162012282608182415)
  ·
    refine ⟨13424998743018423912273623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8949999162012282608182415 13424998743018423912273623)
    ·
      refine ⟨20137498114527635868410435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13424998743018423912273623 20137498114527635868410435)
      ·
        refine ⟨30206247171791453802615653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20137498114527635868410435 30206247171791453802615653)
        ·
          refine ⟨5663671344710897587990435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30206247171791453802615653 5663671344710897587990435)
          ·
            refine ⟨8495507017066346381985653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5663671344710897587990435 8495507017066346381985653)
            ·
              refine ⟨796453782849969973311155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8495507017066346381985653 796453782849969973311155)
              ·
                refine ⟨1194680674274954959966733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796453782849969973311155 1194680674274954959966733)
                ·
                  refine ⟨448005252853108109987525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194680674274954959966733 448005252853108109987525)
                  ·
                    refine ⟨84000984909957770622661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 448005252853108109987525 84000984909957770622661)
                    ·
                      rfl

theorem cell22_245387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 4].length) (baseStart_245387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245387 prefixEnd_245387 := by exact prefixLift 245387
  have htrace : WordTrace (prefixWord ++ tailWord_245387) baseStart_245387 baseEnd_245387 := by
    simpa [prefixWord, tailWord_245387, baseEnd_245387] using wordTrace_append hprefix tailTrace_245387
  have hstable : (prefixWord ++ tailWord_245387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245387).length < 2 ^ (prefixWord ++ tailWord_245387).sum := by decide
  have hdescent : baseEnd_245387 < baseStart_245387 := by decide
  rcases family_descends (prefixWord ++ tailWord_245387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245432 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 4, 4]
def baseStart_245432 : Nat := 118140960795 + 245432 * 2 ^ 59
def prefixEnd_245432 : Nat := 4983230072969 + 3 ^ 40 * 245432 * 2
def baseEnd_245432 : Nat := 84016389329592653247523

theorem tailTrace_245432 : CollatzResearch.WordTrace tailWord_245432 prefixEnd_245432 84016389329592653247523 := by
  unfold tailWord_245432
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475820223424627646785275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5967760297899503529047033 4475820223424627646785275)
  ·
    refine ⟨6713730335136941470177913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4475820223424627646785275 6713730335136941470177913)
    ·
      refine ⟨5035297751352706102633435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6713730335136941470177913 5035297751352706102633435)
      ·
        refine ⟨7552946627029059153950153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5035297751352706102633435 7552946627029059153950153)
        ·
          refine ⟨5664709970271794365462615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7552946627029059153950153 5664709970271794365462615)
          ·
            refine ⟨8497064955407691548193923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5664709970271794365462615 8497064955407691548193923)
            ·
              refine ⟨12745597433111537322290885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8497064955407691548193923 12745597433111537322290885)
              ·
                refine ⟨2389799518708413247929541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12745597433111537322290885 2389799518708413247929541)
                ·
                  refine ⟨448087409757827483986789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2389799518708413247929541 448087409757827483986789)
                  ·
                    refine ⟨84016389329592653247523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 448087409757827483986789 84016389329592653247523)
                    ·
                      rfl

theorem cell22_245432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_245432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245432 prefixEnd_245432 := by exact prefixLift 245432
  have htrace : WordTrace (prefixWord ++ tailWord_245432) baseStart_245432 baseEnd_245432 := by
    simpa [prefixWord, tailWord_245432, baseEnd_245432] using wordTrace_append hprefix tailTrace_245432
  have hstable : (prefixWord ++ tailWord_245432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245432).length < 2 ^ (prefixWord ++ tailWord_245432).sum := by decide
  have hdescent : baseEnd_245432 < baseStart_245432 := by decide
  rcases family_descends (prefixWord ++ tailWord_245432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245434 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_245434 : Nat := 118140960795 + 245434 * 2 ^ 59
def prefixEnd_245434 : Nat := 4983230072969 + 3 ^ 40 * 245434 * 2
def baseEnd_245434 : Nat := 84017073970465314697517

theorem tailTrace_245434 : CollatzResearch.WordTrace tailWord_245434 prefixEnd_245434 84017073970465314697517 := by
  unfold tailWord_245434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2237928348210502408785839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5967808928561339756762237 2237928348210502408785839)
  ·
    refine ⟨3356892522315753613178759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2237928348210502408785839 3356892522315753613178759)
    ·
      refine ⟨5035338783473630419768139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3356892522315753613178759 5035338783473630419768139)
      ·
        refine ⟨7553008175210445629652209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5035338783473630419768139 7553008175210445629652209)
        ·
          refine ⟨5664756131407834222239157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7553008175210445629652209 5664756131407834222239157)
          ·
            refine ⟨531070887319484458334921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5664756131407834222239157 531070887319484458334921)
            ·
              refine ⟨398303165489613343751191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531070887319484458334921 398303165489613343751191)
              ·
                refine ⟨597454748234420015626787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398303165489613343751191 597454748234420015626787)
                ·
                  refine ⟨896182122351630023440181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597454748234420015626787 896182122351630023440181)
                  ·
                    refine ⟨84017073970465314697517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 896182122351630023440181 84017073970465314697517)
                    ·
                      rfl

theorem cell22_245434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_245434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245434 prefixEnd_245434 := by exact prefixLift 245434
  have htrace : WordTrace (prefixWord ++ tailWord_245434) baseStart_245434 baseEnd_245434 := by
    simpa [prefixWord, tailWord_245434, baseEnd_245434] using wordTrace_append hprefix tailTrace_245434
  have hstable : (prefixWord ++ tailWord_245434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245434).length < 2 ^ (prefixWord ++ tailWord_245434).sum := by decide
  have hdescent : baseEnd_245434 < baseStart_245434 := by decide
  rcases family_descends (prefixWord ++ tailWord_245434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245453 : List Nat := [1, 6, 2, 1, 1, 1, 1, 5, 4]
def baseStart_245453 : Nat := 118140960795 + 245453 * 2 ^ 59
def prefixEnd_245453 : Nat := 4983230072969 + 3 ^ 40 * 245453 * 2
def baseEnd_245453 : Nat := 28007859352918532824153

theorem tailTrace_245453 : CollatzResearch.WordTrace tailWord_245453 prefixEnd_245453 28007859352918532824153 := by
  unfold tailWord_245453
  simp only [CollatzResearch.WordTrace]
  refine ⟨8952406379773175880085013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5968270919848783920056675 8952406379773175880085013)
  ·
    refine ⟨419644049051867619378985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8952406379773175880085013 419644049051867619378985)
    ·
      refine ⟨314733036788900714534239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419644049051867619378985 314733036788900714534239)
      ·
        refine ⟨472099555183351071801359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314733036788900714534239 472099555183351071801359)
        ·
          refine ⟨708149332775026607702039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472099555183351071801359 708149332775026607702039)
          ·
            refine ⟨1062223999162539911553059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708149332775026607702039 1062223999162539911553059)
            ·
              refine ⟨1593335998743809867329589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062223999162539911553059 1593335998743809867329589)
              ·
                refine ⟨149375249882232175062149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1593335998743809867329589 149375249882232175062149)
                ·
                  refine ⟨28007859352918532824153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149375249882232175062149 28007859352918532824153)
                  ·
                    rfl

theorem cell22_245453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_245453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245453 prefixEnd_245453 := by exact prefixLift 245453
  have htrace : WordTrace (prefixWord ++ tailWord_245453) baseStart_245453 baseEnd_245453 := by
    simpa [prefixWord, tailWord_245453, baseEnd_245453] using wordTrace_append hprefix tailTrace_245453
  have hstable : (prefixWord ++ tailWord_245453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245453).length < 2 ^ (prefixWord ++ tailWord_245453).sum := by decide
  have hdescent : baseEnd_245453 < baseStart_245453 := by decide
  rcases family_descends (prefixWord ++ tailWord_245453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245468 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 4, 3]
def baseStart_245468 : Nat := 118140960795 + 245468 * 2 ^ 59
def prefixEnd_245468 : Nat := 4983230072969 + 3 ^ 40 * 245468 * 2
def baseEnd_245468 : Nat := 84028712865300559347413

theorem tailTrace_245468 : CollatzResearch.WordTrace tailWord_245468 prefixEnd_245468 84028712865300559347413 := by
  unfold tailWord_245468
  simp only [CollatzResearch.WordTrace]
  refine ⟨4476476737359416720940529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5968635649812555627920705 4476476737359416720940529)
  ·
    refine ⟨3357357553019562540705397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4476476737359416720940529 3357357553019562540705397)
    ·
      refine ⟨314752270595583988191131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3357357553019562540705397 314752270595583988191131)
      ·
        refine ⟨472128405893375982286697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314752270595583988191131 472128405893375982286697)
        ·
          refine ⟨354096304420031986715023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472128405893375982286697 354096304420031986715023)
          ·
            refine ⟨531144456630047980072535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354096304420031986715023 531144456630047980072535)
            ·
              refine ⟨796716684945071970108803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531144456630047980072535 796716684945071970108803)
              ·
                refine ⟨1195075027417607955163205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796716684945071970108803 1195075027417607955163205)
                ·
                  refine ⟨224076567640801491593101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1195075027417607955163205 224076567640801491593101)
                  ·
                    refine ⟨84028712865300559347413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224076567640801491593101 84028712865300559347413)
                    ·
                      rfl

theorem cell22_245468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_245468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245468 prefixEnd_245468 := by exact prefixLift 245468
  have htrace : WordTrace (prefixWord ++ tailWord_245468) baseStart_245468 baseEnd_245468 := by
    simpa [prefixWord, tailWord_245468, baseEnd_245468] using wordTrace_append hprefix tailTrace_245468
  have hstable : (prefixWord ++ tailWord_245468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245468).length < 2 ^ (prefixWord ++ tailWord_245468).sum := by decide
  have hdescent : baseEnd_245468 < baseStart_245468 := by decide
  rcases family_descends (prefixWord ++ tailWord_245468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245507 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 1, 7]
def baseStart_245507 : Nat := 118140960795 + 245507 * 2 ^ 59
def prefixEnd_245507 : Nat := 4983230072969 + 3 ^ 40 * 245507 * 2
def baseEnd_245507 : Nat := 84042063362317457622293

theorem tailTrace_245507 : CollatzResearch.WordTrace tailWord_245507 prefixEnd_245507 84042063362317457622293 := by
  unfold tailWord_245507
  simp only [CollatzResearch.WordTrace]
  refine ⟨8954375921577543102550775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5969583947718362068367183 8954375921577543102550775)
  ·
    refine ⟨13431563882366314653826163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8954375921577543102550775 13431563882366314653826163)
    ·
      refine ⟨20147345823549471980739245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13431563882366314653826163 20147345823549471980739245)
      ·
        refine ⟨7555254683831051992777217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20147345823549471980739245 7555254683831051992777217)
        ·
          refine ⟨5666441012873288994582913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7555254683831051992777217 5666441012873288994582913)
          ·
            refine ⟨4249830759654966745937185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5666441012873288994582913 4249830759654966745937185)
            ·
              refine ⟨3187373069741225059452889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4249830759654966745937185 3187373069741225059452889)
              ·
                refine ⟨2390529802305918794589667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3187373069741225059452889 2390529802305918794589667)
                ·
                  refine ⟨3585794703458878191884501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390529802305918794589667 3585794703458878191884501)
                  ·
                    refine ⟨84042063362317457622293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3585794703458878191884501 84042063362317457622293)
                    ·
                      rfl

theorem cell22_245507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_245507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245507 prefixEnd_245507 := by exact prefixLift 245507
  have htrace : WordTrace (prefixWord ++ tailWord_245507) baseStart_245507 baseEnd_245507 := by
    simpa [prefixWord, tailWord_245507, baseEnd_245507] using wordTrace_append hprefix tailTrace_245507
  have hstable : (prefixWord ++ tailWord_245507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245507).length < 2 ^ (prefixWord ++ tailWord_245507).sum := by decide
  have hdescent : baseEnd_245507 < baseStart_245507 := by decide
  rcases family_descends (prefixWord ++ tailWord_245507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245517 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_245517 : Nat := 118140960795 + 245517 * 2 ^ 59
def prefixEnd_245517 : Nat := 4983230072969 + 3 ^ 40 * 245517 * 2
def baseEnd_245517 : Nat := 84045486566680764872263

theorem tailTrace_245517 : CollatzResearch.WordTrace tailWord_245517 prefixEnd_245517 84045486566680764872263 := by
  unfold tailWord_245517
  simp only [CollatzResearch.WordTrace]
  refine ⟨8954740651541314810414805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5969827101027543206943203 8954740651541314810414805)
  ·
    refine ⟨209876734020499565869097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8954740651541314810414805 209876734020499565869097)
    ·
      refine ⟨157407550515374674401823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209876734020499565869097 157407550515374674401823)
      ·
        refine ⟨236111325773062011602735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157407550515374674401823 236111325773062011602735)
        ·
          refine ⟨354166988659593017404103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236111325773062011602735 354166988659593017404103)
          ·
            refine ⟨531250482989389526106155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354166988659593017404103 531250482989389526106155)
            ·
              refine ⟨796875724484084289159233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531250482989389526106155 796875724484084289159233)
              ·
                refine ⟨597656793363063216869425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796875724484084289159233 597656793363063216869425)
                ·
                  refine ⟨448242595022297412652069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 597656793363063216869425 448242595022297412652069)
                  ·
                    refine ⟨84045486566680764872263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 448242595022297412652069 84045486566680764872263)
                    ·
                      rfl

theorem cell22_245517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_245517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245517 prefixEnd_245517 := by exact prefixLift 245517
  have htrace : WordTrace (prefixWord ++ tailWord_245517) baseStart_245517 baseEnd_245517 := by
    simpa [prefixWord, tailWord_245517, baseEnd_245517] using wordTrace_append hprefix tailTrace_245517
  have hstable : (prefixWord ++ tailWord_245517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245517).length < 2 ^ (prefixWord ++ tailWord_245517).sum := by decide
  have hdescent : baseEnd_245517 < baseStart_245517 := by decide
  rcases family_descends (prefixWord ++ tailWord_245517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245530 : List Nat := [3, 1, 1, 3, 2, 3, 3, 2, 1, 3]
def baseStart_245530 : Nat := 118140960795 + 245530 * 2 ^ 59
def prefixEnd_245530 : Nat := 4983230072969 + 3 ^ 40 * 245530 * 2
def baseEnd_245530 : Nat := 84049936732353064297223

theorem tailTrace_245530 : CollatzResearch.WordTrace tailWord_245530 prefixEnd_245530 84049936732353064297223 := by
  unfold tailWord_245530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2238803700123554507659511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5970143200329478687092029 2238803700123554507659511)
  ·
    refine ⟨3358205550185331761489267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2238803700123554507659511 3358205550185331761489267)
    ·
      refine ⟨5037308325277997642233901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358205550185331761489267 5037308325277997642233901)
      ·
        refine ⟨1888990621979249115837713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5037308325277997642233901 1888990621979249115837713)
        ·
          refine ⟨1416742966484436836878285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1888990621979249115837713 1416742966484436836878285)
          ·
            refine ⟨531278612431663813829357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1416742966484436836878285 531278612431663813829357)
            ·
              refine ⟨199229479661873930186009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 531278612431663813829357 199229479661873930186009)
              ·
                refine ⟨149422109746405447639507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199229479661873930186009 149422109746405447639507)
                ·
                  refine ⟨224133164619608171459261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149422109746405447639507 224133164619608171459261)
                  ·
                    refine ⟨84049936732353064297223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224133164619608171459261 84049936732353064297223)
                    ·
                      rfl

theorem cell22_245530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_245530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245530 prefixEnd_245530 := by exact prefixLift 245530
  have htrace : WordTrace (prefixWord ++ tailWord_245530) baseStart_245530 baseEnd_245530 := by
    simpa [prefixWord, tailWord_245530, baseEnd_245530] using wordTrace_append hprefix tailTrace_245530
  have hstable : (prefixWord ++ tailWord_245530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245530).length < 2 ^ (prefixWord ++ tailWord_245530).sum := by decide
  have hdescent : baseEnd_245530 < baseStart_245530 := by decide
  rcases family_descends (prefixWord ++ tailWord_245530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245588 : List Nat := [2, 4, 1, 1, 3, 2, 1, 4, 4]
def baseStart_245588 : Nat := 118140960795 + 245588 * 2 ^ 59
def prefixEnd_245588 : Nat := 4983230072969 + 3 ^ 40 * 245588 * 2
def baseEnd_245588 : Nat := 28023263772553415449015

theorem tailTrace_245588 : CollatzResearch.WordTrace tailWord_245588 prefixEnd_245588 28023263772553415449015 := by
  unfold tailWord_245588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4478665117142046968124709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5971553489522729290832945 4478665117142046968124709)
  ·
    refine ⟨839749709464133806523383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4478665117142046968124709 839749709464133806523383)
    ·
      refine ⟨1259624564196200709785075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 839749709464133806523383 1259624564196200709785075)
      ·
        refine ⟨1889436846294301064677613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1259624564196200709785075 1889436846294301064677613)
        ·
          refine ⟨708538817360362899254105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1889436846294301064677613 708538817360362899254105)
          ·
            refine ⟨531404113020272174440579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708538817360362899254105 531404113020272174440579)
            ·
              refine ⟨797106169530408261660869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531404113020272174440579 797106169530408261660869)
              ·
                refine ⟨149457406786951549061413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 797106169530408261660869 149457406786951549061413)
                ·
                  refine ⟨28023263772553415449015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149457406786951549061413 28023263772553415449015)
                  ·
                    rfl

theorem cell22_245588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_245588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245588 prefixEnd_245588 := by exact prefixLift 245588
  have htrace : WordTrace (prefixWord ++ tailWord_245588) baseStart_245588 baseEnd_245588 := by
    simpa [prefixWord, tailWord_245588, baseEnd_245588] using wordTrace_append hprefix tailTrace_245588
  have hstable : (prefixWord ++ tailWord_245588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245588).length < 2 ^ (prefixWord ++ tailWord_245588).sum := by decide
  have hdescent : baseEnd_245588 < baseStart_245588 := by decide
  rcases family_descends (prefixWord ++ tailWord_245588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245599 : List Nat := [1, 1, 2, 3, 1, 4, 3, 7]
def baseStart_245599 : Nat := 118140960795 + 245599 * 2 ^ 59
def prefixEnd_245599 : Nat := 4983230072969 + 3 ^ 40 * 245599 * 2
def baseEnd_245599 : Nat := 9341506315828876035779

theorem tailTrace_245599 : CollatzResearch.WordTrace tailWord_245599 prefixEnd_245599 9341506315828876035779 := by
  unfold tailWord_245599
  simp only [CollatzResearch.WordTrace]
  refine ⟨8957731437244242814899851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5971820958162828543266567 8957731437244242814899851)
  ·
    refine ⟨13436597155866364222349777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8957731437244242814899851 13436597155866364222349777)
    ·
      refine ⟨10077447866899773166762333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13436597155866364222349777 10077447866899773166762333)
      ·
        refine ⟨3779042950087414937535875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10077447866899773166762333 3779042950087414937535875)
        ·
          refine ⟨5668564425131122406303813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779042950087414937535875 5668564425131122406303813)
          ·
            refine ⟨1062855829712085451181965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5668564425131122406303813 1062855829712085451181965)
            ·
              refine ⟨398570936142032044193237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1062855829712085451181965 398570936142032044193237)
              ·
                refine ⟨9341506315828876035779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 398570936142032044193237 9341506315828876035779)
                ·
                  rfl

theorem cell22_245599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 7].length) (baseStart_245599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245599 prefixEnd_245599 := by exact prefixLift 245599
  have htrace : WordTrace (prefixWord ++ tailWord_245599) baseStart_245599 baseEnd_245599 := by
    simpa [prefixWord, tailWord_245599, baseEnd_245599] using wordTrace_append hprefix tailTrace_245599
  have hstable : (prefixWord ++ tailWord_245599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245599).length < 2 ^ (prefixWord ++ tailWord_245599).sum := by decide
  have hdescent : baseEnd_245599 < baseStart_245599 := by decide
  rcases family_descends (prefixWord ++ tailWord_245599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245654 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_245654 : Nat := 118140960795 + 245654 * 2 ^ 59
def prefixEnd_245654 : Nat := 4983230072969 + 3 ^ 40 * 245654 * 2
def baseEnd_245654 : Nat := 84092384466458074196843

theorem tailTrace_245654 : CollatzResearch.WordTrace tailWord_245654 prefixEnd_245654 84092384466458074196843 := by
  unfold tailWord_245654
  simp only [CollatzResearch.WordTrace]
  refine ⟨559983590752811700509501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5973158301363324805434677 559983590752811700509501)
  ·
    refine ⟨209993846532304387691063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 559983590752811700509501 209993846532304387691063)
    ·
      refine ⟨314990769798456581536595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209993846532304387691063 314990769798456581536595)
      ·
        refine ⟨472486154697684872304893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314990769798456581536595 472486154697684872304893)
        ·
          refine ⟨177182308011631827114335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472486154697684872304893 177182308011631827114335)
          ·
            refine ⟨265773462017447740671503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177182308011631827114335 265773462017447740671503)
            ·
              refine ⟨398660193026171611007255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265773462017447740671503 398660193026171611007255)
              ·
                refine ⟨597990289539257416510883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398660193026171611007255 597990289539257416510883)
                ·
                  refine ⟨896985434308886124766325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597990289539257416510883 896985434308886124766325)
                  ·
                    refine ⟨84092384466458074196843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 896985434308886124766325 84092384466458074196843)
                    ·
                      rfl

theorem cell22_245654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_245654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245654 prefixEnd_245654 := by exact prefixLift 245654
  have htrace : WordTrace (prefixWord ++ tailWord_245654) baseStart_245654 baseEnd_245654 := by
    simpa [prefixWord, tailWord_245654, baseEnd_245654] using wordTrace_append hprefix tailTrace_245654
  have hstable : (prefixWord ++ tailWord_245654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245654).length < 2 ^ (prefixWord ++ tailWord_245654).sum := by decide
  have hdescent : baseEnd_245654 < baseStart_245654 := by decide
  rcases family_descends (prefixWord ++ tailWord_245654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245706 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 6]
def baseStart_245706 : Nat := 118140960795 + 245706 * 2 ^ 59
def prefixEnd_245706 : Nat := 4983230072969 + 3 ^ 40 * 245706 * 2
def baseEnd_245706 : Nat := 28036728376382423965561

theorem tailTrace_245706 : CollatzResearch.WordTrace tailWord_245706 prefixEnd_245706 28036728376382423965561 := by
  unfold tailWord_245706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2240408511964150022261243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5974422698571066726029981 2240408511964150022261243)
  ·
    refine ⟨3360612767946225033391865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2240408511964150022261243 3360612767946225033391865)
    ·
      refine ⟨2520459575959668775043899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3360612767946225033391865 2520459575959668775043899)
      ·
        refine ⟨3780689363939503162565849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2520459575959668775043899 3780689363939503162565849)
        ·
          refine ⟨2835517022954627371924387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3780689363939503162565849 2835517022954627371924387)
          ·
            refine ⟨4253275534431941057886581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835517022954627371924387 4253275534431941057886581)
            ·
              refine ⟨398744581352994474176867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4253275534431941057886581 398744581352994474176867)
              ·
                refine ⟨598116872029491711265301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398744581352994474176867 598116872029491711265301)
                ·
                  refine ⟨28036728376382423965561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 598116872029491711265301 28036728376382423965561)
                  ·
                    rfl

theorem cell22_245706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_245706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245706 prefixEnd_245706 := by exact prefixLift 245706
  have htrace : WordTrace (prefixWord ++ tailWord_245706) baseStart_245706 baseEnd_245706 := by
    simpa [prefixWord, tailWord_245706, baseEnd_245706] using wordTrace_append hprefix tailTrace_245706
  have hstable : (prefixWord ++ tailWord_245706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245706).length < 2 ^ (prefixWord ++ tailWord_245706).sum := by decide
  have hdescent : baseEnd_245706 < baseStart_245706 := by decide
  rcases family_descends (prefixWord ++ tailWord_245706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245811 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 2, 5]
def baseStart_245811 : Nat := 118140960795 + 245811 * 2 ^ 59
def prefixEnd_245811 : Nat := 4983230072969 + 3 ^ 40 * 245811 * 2
def baseEnd_245811 : Nat := 84146128774961998021361

theorem tailTrace_245811 : CollatzResearch.WordTrace tailWord_245811 prefixEnd_245811 84146128774961998021361 := by
  unfold tailWord_245811
  simp only [CollatzResearch.WordTrace]
  refine ⟨8965463712476203021617287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5976975808317468681078191 8965463712476203021617287)
  ·
    refine ⟨13448195568714304532425931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8965463712476203021617287 13448195568714304532425931)
    ·
      refine ⟨20172293353071456798638897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13448195568714304532425931 20172293353071456798638897)
      ·
        refine ⟨15129220014803592598979173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20172293353071456798638897 15129220014803592598979173)
        ·
          refine ⟨2836728752775673612308595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15129220014803592598979173 2836728752775673612308595)
          ·
            refine ⟨4255093129163510418462893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836728752775673612308595 4255093129163510418462893)
            ·
              refine ⟨1595659923436316406923585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4255093129163510418462893 1595659923436316406923585)
              ·
                refine ⟨1196744942577237305192689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1595659923436316406923585 1196744942577237305192689)
                ·
                  refine ⟨897558706932927978894517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1196744942577237305192689 897558706932927978894517)
                  ·
                    refine ⟨84146128774961998021361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 897558706932927978894517 84146128774961998021361)
                    ·
                      rfl

theorem cell22_245811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 5].length) (baseStart_245811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245811 prefixEnd_245811 := by exact prefixLift 245811
  have htrace : WordTrace (prefixWord ++ tailWord_245811) baseStart_245811 baseEnd_245811 := by
    simpa [prefixWord, tailWord_245811, baseEnd_245811] using wordTrace_append hprefix tailTrace_245811
  have hstable : (prefixWord ++ tailWord_245811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245811).length < 2 ^ (prefixWord ++ tailWord_245811).sum := by decide
  have hdescent : baseEnd_245811 < baseStart_245811 := by decide
  rcases family_descends (prefixWord ++ tailWord_245811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245813 : List Nat := [1, 3, 3, 1, 1, 1, 5, 2, 5]
def baseStart_245813 : Nat := 118140960795 + 245813 * 2 ^ 59
def prefixEnd_245813 : Nat := 4983230072969 + 3 ^ 40 * 245813 * 2
def baseEnd_245813 : Nat := 28048937805278219823785

theorem tailTrace_245813 : CollatzResearch.WordTrace tailWord_245813 prefixEnd_245813 28048937805278219823785 := by
  unfold tailWord_245813
  simp only [CollatzResearch.WordTrace]
  refine ⟨8965536658468957363190093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5977024438979304908793395 8965536658468957363190093)
  ·
    refine ⟨3362076246925859011196285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8965536658468957363190093 3362076246925859011196285)
    ·
      refine ⟨1260778592597197129198607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3362076246925859011196285 1260778592597197129198607)
      ·
        refine ⟨1891167888895795693797911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260778592597197129198607 1891167888895795693797911)
        ·
          refine ⟨2836751833343693540696867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891167888895795693797911 2836751833343693540696867)
          ·
            refine ⟨4255127750015540311045301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836751833343693540696867 4255127750015540311045301)
            ·
              refine ⟨398918226563956904160497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4255127750015540311045301 398918226563956904160497)
              ·
                refine ⟨299188669922967678120373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398918226563956904160497 299188669922967678120373)
                ·
                  refine ⟨28048937805278219823785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 299188669922967678120373 28048937805278219823785)
                  ·
                    rfl

theorem cell22_245813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_245813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245813 prefixEnd_245813 := by exact prefixLift 245813
  have htrace : WordTrace (prefixWord ++ tailWord_245813) baseStart_245813 baseEnd_245813 := by
    simpa [prefixWord, tailWord_245813, baseEnd_245813] using wordTrace_append hprefix tailTrace_245813
  have hstable : (prefixWord ++ tailWord_245813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245813).length < 2 ^ (prefixWord ++ tailWord_245813).sum := by decide
  have hdescent : baseEnd_245813 < baseStart_245813 := by decide
  rcases family_descends (prefixWord ++ tailWord_245813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245873 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 4, 3]
def baseStart_245873 : Nat := 118140960795 + 245873 * 2 ^ 59
def prefixEnd_245873 : Nat := 4983230072969 + 3 ^ 40 * 245873 * 2
def baseEnd_245873 : Nat := 84167352642014502971171

theorem tailTrace_245873 : CollatzResearch.WordTrace tailWord_245873 prefixEnd_245873 84167352642014502971171 := by
  unfold tailWord_245873
  simp only [CollatzResearch.WordTrace]
  refine ⟨8967725038251587610374273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5978483358834391740249515 8967725038251587610374273)
  ·
    refine ⟨6725793778688690707780705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8967725038251587610374273 6725793778688690707780705)
    ·
      refine ⟨5044345334016518030835529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6725793778688690707780705 5044345334016518030835529)
      ·
        refine ⟨3783259000512388523126647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5044345334016518030835529 3783259000512388523126647)
        ·
          refine ⟨5674888500768582784689971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783259000512388523126647 5674888500768582784689971)
          ·
            refine ⟨8512332751152874177034957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5674888500768582784689971 8512332751152874177034957)
            ·
              refine ⟨3192124781682327816388109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8512332751152874177034957 3192124781682327816388109)
              ·
                refine ⟨1197046793130872931145541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3192124781682327816388109 1197046793130872931145541)
                ·
                  refine ⟨224446273712038674589789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1197046793130872931145541 224446273712038674589789)
                  ·
                    refine ⟨84167352642014502971171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224446273712038674589789 84167352642014502971171)
                    ·
                      rfl

theorem cell22_245873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_245873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245873 prefixEnd_245873 := by exact prefixLift 245873
  have htrace : WordTrace (prefixWord ++ tailWord_245873) baseStart_245873 baseEnd_245873 := by
    simpa [prefixWord, tailWord_245873, baseEnd_245873] using wordTrace_append hprefix tailTrace_245873
  have hstable : (prefixWord ++ tailWord_245873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245873).length < 2 ^ (prefixWord ++ tailWord_245873).sum := by decide
  have hdescent : baseEnd_245873 < baseStart_245873 := by decide
  rcases family_descends (prefixWord ++ tailWord_245873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245931 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 13]
def baseStart_245931 : Nat := 118140960795 + 245931 * 2 ^ 59
def prefixEnd_245931 : Nat := 4983230072969 + 3 ^ 40 * 245931 * 2
def baseEnd_245931 : Nat := 28062402409107228340331

theorem tailTrace_245931 : CollatzResearch.WordTrace tailWord_245931 prefixEnd_245931 28062402409107228340331 := by
  unfold tailWord_245931
  simp only [CollatzResearch.WordTrace]
  refine ⟨8969840472041463515985647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5979893648027642343990431 8969840472041463515985647)
  ·
    refine ⟨13454760708062195273978471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8969840472041463515985647 13454760708062195273978471)
    ·
      refine ⟨20182141062093292910967707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13454760708062195273978471 20182141062093292910967707)
      ·
        refine ⟨30273211593139939366451561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20182141062093292910967707 30273211593139939366451561)
        ·
          refine ⟨22704908694854954524838671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30273211593139939366451561 22704908694854954524838671)
          ·
            refine ⟨34057363042282431787258007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22704908694854954524838671 34057363042282431787258007)
            ·
              refine ⟨51086044563423647680887011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34057363042282431787258007 51086044563423647680887011)
              ·
                refine ⟨76629066845135471521330517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51086044563423647680887011 76629066845135471521330517)
                ·
                  refine ⟨28062402409107228340331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 76629066845135471521330517 28062402409107228340331)
                  ·
                    rfl

theorem cell22_245931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 13].length) (baseStart_245931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245931 prefixEnd_245931 := by exact prefixLift 245931
  have htrace : WordTrace (prefixWord ++ tailWord_245931) baseStart_245931 baseEnd_245931 := by
    simpa [prefixWord, tailWord_245931, baseEnd_245931] using wordTrace_append hprefix tailTrace_245931
  have hstable : (prefixWord ++ tailWord_245931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245931).length < 2 ^ (prefixWord ++ tailWord_245931).sum := by decide
  have hdescent : baseEnd_245931 < baseStart_245931 := by decide
  rcases family_descends (prefixWord ++ tailWord_245931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245937 : List Nat := [1, 2, 2, 5, 3, 1, 1, 7]
def baseStart_245937 : Nat := 118140960795 + 245937 * 2 ^ 59
def prefixEnd_245937 : Nat := 4983230072969 + 3 ^ 40 * 245937 * 2
def baseEnd_245937 : Nat := 9354362349993296596775

theorem tailTrace_245937 : CollatzResearch.WordTrace tailWord_245937 prefixEnd_245937 9354362349993296596775 := by
  unfold tailWord_245937
  simp only [CollatzResearch.WordTrace]
  refine ⟨8970059310019726540704065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5980039540013151027136043 8970059310019726540704065)
  ·
    refine ⟨6727544482514794905528049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8970059310019726540704065 6727544482514794905528049)
    ·
      refine ⟨5045658361886096179146037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6727544482514794905528049 5045658361886096179146037)
      ·
        refine ⟨473030471426821516794941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5045658361886096179146037 473030471426821516794941)
        ·
          refine ⟨177386426785058068798103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473030471426821516794941 177386426785058068798103)
          ·
            refine ⟨266079640177587103197155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177386426785058068798103 266079640177587103197155)
            ·
              refine ⟨399119460266380654795733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266079640177587103197155 399119460266380654795733)
              ·
                refine ⟨9354362349993296596775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 399119460266380654795733 9354362349993296596775)
                ·
                  rfl

theorem cell22_245937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 7].length) (baseStart_245937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245937 prefixEnd_245937 := by exact prefixLift 245937
  have htrace : WordTrace (prefixWord ++ tailWord_245937) baseStart_245937 baseEnd_245937 := by
    simpa [prefixWord, tailWord_245937, baseEnd_245937] using wordTrace_append hprefix tailTrace_245937
  have hstable : (prefixWord ++ tailWord_245937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245937).length < 2 ^ (prefixWord ++ tailWord_245937).sum := by decide
  have hdescent : baseEnd_245937 < baseStart_245937 := by decide
  rcases family_descends (prefixWord ++ tailWord_245937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245954 : List Nat := [3, 5, 1, 1, 1, 2, 3, 6]
def baseStart_245954 : Nat := 118140960795 + 245954 * 2 ^ 59
def prefixEnd_245954 : Nat := 4983230072969 + 3 ^ 40 * 245954 * 2
def baseEnd_245954 : Nat := 9355008955261921299547

theorem tailTrace_245954 : CollatzResearch.WordTrace tailWord_245954 prefixEnd_245954 9355008955261921299547 := by
  unfold tailWord_245954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2242669837739534611018229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5980452900638758962715277 2242669837739534611018229)
  ·
    refine ⟨210250297288081369782959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2242669837739534611018229 210250297288081369782959)
    ·
      refine ⟨315375445932122054674439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210250297288081369782959 315375445932122054674439)
      ·
        refine ⟨473063168898183082011659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315375445932122054674439 473063168898183082011659)
        ·
          refine ⟨709594753347274623017489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473063168898183082011659 709594753347274623017489)
          ·
            refine ⟨532196065010455967263117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709594753347274623017489 532196065010455967263117)
            ·
              refine ⟨199573524378920987723669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 532196065010455967263117 199573524378920987723669)
              ·
                refine ⟨9355008955261921299547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199573524378920987723669 9355008955261921299547)
                ·
                  rfl

theorem cell22_245954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_245954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_245954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_245954 prefixEnd_245954 := by exact prefixLift 245954
  have htrace : WordTrace (prefixWord ++ tailWord_245954) baseStart_245954 baseEnd_245954 := by
    simpa [prefixWord, tailWord_245954, baseEnd_245954] using wordTrace_append hprefix tailTrace_245954
  have hstable : (prefixWord ++ tailWord_245954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245954).length < 2 ^ (prefixWord ++ tailWord_245954).sum := by decide
  have hdescent : baseEnd_245954 < baseStart_245954 := by decide
  rcases family_descends (prefixWord ++ tailWord_245954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246012 : List Nat := [2, 2, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_246012 : Nat := 118140960795 + 246012 * 2 ^ 59
def prefixEnd_246012 : Nat := 4983230072969 + 3 ^ 40 * 246012 * 2
def baseEnd_246012 : Nat := 84214935182664473745745

theorem tailTrace_246012 : CollatzResearch.WordTrace tailWord_246012 prefixEnd_246012 84214935182664473745745 := by
  unfold tailWord_246012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4486397392374007174842145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5981863189832009566456193 4486397392374007174842145)
  ·
    refine ⟨3364798044280505381131609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4486397392374007174842145 3364798044280505381131609)
    ·
      refine ⟨2523598533210379035848707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3364798044280505381131609 2523598533210379035848707)
      ·
        refine ⟨3785397799815568553773061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523598533210379035848707 3785397799815568553773061)
        ·
          refine ⟨709762087465419103832449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3785397799815568553773061 709762087465419103832449)
          ·
            refine ⟨532321565599064327874337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709762087465419103832449 532321565599064327874337)
            ·
              refine ⟨399241174199298245905753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532321565599064327874337 399241174199298245905753)
              ·
                refine ⟨299430880649473684429315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399241174199298245905753 299430880649473684429315)
                ·
                  refine ⟨449146320974210526643973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299430880649473684429315 449146320974210526643973)
                  ·
                    refine ⟨84214935182664473745745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 449146320974210526643973 84214935182664473745745)
                    ·
                      rfl

theorem cell22_246012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_246012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246012 prefixEnd_246012 := by exact prefixLift 246012
  have htrace : WordTrace (prefixWord ++ tailWord_246012) baseStart_246012 baseEnd_246012 := by
    simpa [prefixWord, tailWord_246012, baseEnd_246012] using wordTrace_append hprefix tailTrace_246012
  have hstable : (prefixWord ++ tailWord_246012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246012).length < 2 ^ (prefixWord ++ tailWord_246012).sum := by decide
  have hdescent : baseEnd_246012 < baseStart_246012 := by decide
  rcases family_descends (prefixWord ++ tailWord_246012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246025 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 4, 3]
def baseStart_246025 : Nat := 118140960795 + 246025 * 2 ^ 59
def prefixEnd_246025 : Nat := 4983230072969 + 3 ^ 40 * 246025 * 2
def baseEnd_246025 : Nat := 84219385348336773170705

theorem tailTrace_246025 : CollatzResearch.WordTrace tailWord_246025 prefixEnd_246025 84219385348336773170705 := by
  unfold tailWord_246025
  simp only [CollatzResearch.WordTrace]
  refine ⟨8973268933700917569907529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5982179289133945046605019 8973268933700917569907529)
  ·
    refine ⟨6729951700275688177430647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8973268933700917569907529 6729951700275688177430647)
    ·
      refine ⟨10094927550413532266145971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6729951700275688177430647 10094927550413532266145971)
      ·
        refine ⟨15142391325620298399218957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10094927550413532266145971 15142391325620298399218957)
        ·
          refine ⟨5678396747107611899707109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15142391325620298399218957 5678396747107611899707109)
          ·
            refine ⟨1064699390082677231195083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5678396747107611899707109 1064699390082677231195083)
            ·
              refine ⟨1597049085124015846792625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064699390082677231195083 1597049085124015846792625)
              ·
                refine ⟨1197786813843011885094469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597049085124015846792625 1197786813843011885094469)
                ·
                  refine ⟨224585027595564728455213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1197786813843011885094469 224585027595564728455213)
                  ·
                    refine ⟨84219385348336773170705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224585027595564728455213 84219385348336773170705)
                    ·
                      rfl

theorem cell22_246025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 3].length) (baseStart_246025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246025 prefixEnd_246025 := by exact prefixLift 246025
  have htrace : WordTrace (prefixWord ++ tailWord_246025) baseStart_246025 baseEnd_246025 := by
    simpa [prefixWord, tailWord_246025, baseEnd_246025] using wordTrace_append hprefix tailTrace_246025
  have hstable : (prefixWord ++ tailWord_246025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246025).length < 2 ^ (prefixWord ++ tailWord_246025).sum := by decide
  have hdescent : baseEnd_246025 < baseStart_246025 := by decide
  rcases family_descends (prefixWord ++ tailWord_246025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246040 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 2, 4]
def baseStart_246040 : Nat := 118140960795 + 246040 * 2 ^ 59
def prefixEnd_246040 : Nat := 4983230072969 + 3 ^ 40 * 246040 * 2
def baseEnd_246040 : Nat := 84224520154881734045659

theorem tailTrace_246040 : CollatzResearch.WordTrace tailWord_246040 prefixEnd_246040 84224520154881734045659 := by
  unfold tailWord_246040
  simp only [CollatzResearch.WordTrace]
  refine ⟨4486908014323287565851787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5982544019097716754469049 4486908014323287565851787)
  ·
    refine ⟨6730362021484931348777681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4486908014323287565851787 6730362021484931348777681)
    ·
      refine ⟨5047771516113698511583261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6730362021484931348777681 5047771516113698511583261)
      ·
        refine ⟨1892914318542636941843723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5047771516113698511583261 1892914318542636941843723)
        ·
          refine ⟨2839371477813955412765585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892914318542636941843723 2839371477813955412765585)
          ·
            refine ⟨2129528608360466559574189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2839371477813955412765585 2129528608360466559574189)
            ·
              refine ⟨798573228135174959840321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2129528608360466559574189 798573228135174959840321)
              ·
                refine ⟨598929921101381219880241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798573228135174959840321 598929921101381219880241)
                ·
                  refine ⟨449197440826035914910181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 598929921101381219880241 449197440826035914910181)
                  ·
                    refine ⟨84224520154881734045659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 449197440826035914910181 84224520154881734045659)
                    ·
                      rfl

theorem cell22_246040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_246040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246040 prefixEnd_246040 := by exact prefixLift 246040
  have htrace : WordTrace (prefixWord ++ tailWord_246040) baseStart_246040 baseEnd_246040 := by
    simpa [prefixWord, tailWord_246040, baseEnd_246040] using wordTrace_append hprefix tailTrace_246040
  have hstable : (prefixWord ++ tailWord_246040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246040).length < 2 ^ (prefixWord ++ tailWord_246040).sum := by decide
  have hdescent : baseEnd_246040 < baseStart_246040 := by decide
  rcases family_descends (prefixWord ++ tailWord_246040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246083 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 9]
def baseStart_246083 : Nat := 118140960795 + 246083 * 2 ^ 59
def prefixEnd_246083 : Nat := 4983230072969 + 3 ^ 40 * 246083 * 2
def baseEnd_246083 : Nat := 28079746644547985073509

theorem tailTrace_246083 : CollatzResearch.WordTrace tailWord_246083 prefixEnd_246083 28079746644547985073509 := by
  unfold tailWord_246083
  simp only [CollatzResearch.WordTrace]
  refine ⟨8975384367490793475518903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5983589578327195650345935 8975384367490793475518903)
  ·
    refine ⟨13463076551236190213278355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8975384367490793475518903 13463076551236190213278355)
    ·
      refine ⟨20194614826854285319917533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13463076551236190213278355 20194614826854285319917533)
      ·
        refine ⟨7572980560070356994969075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20194614826854285319917533 7572980560070356994969075)
        ·
          refine ⟨11359470840105535492453613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7572980560070356994969075 11359470840105535492453613)
          ·
            refine ⟨4259801565039575809670105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11359470840105535492453613 4259801565039575809670105)
            ·
              refine ⟨3194851173779681857252579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4259801565039575809670105 3194851173779681857252579)
              ·
                refine ⟨4792276760669522785878869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194851173779681857252579 4792276760669522785878869)
                ·
                  refine ⟨28079746644547985073509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4792276760669522785878869 28079746644547985073509)
                  ·
                    rfl

theorem cell22_246083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 9].length) (baseStart_246083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246083 prefixEnd_246083 := by exact prefixLift 246083
  have htrace : WordTrace (prefixWord ++ tailWord_246083) baseStart_246083 baseEnd_246083 := by
    simpa [prefixWord, tailWord_246083, baseEnd_246083] using wordTrace_append hprefix tailTrace_246083
  have hstable : (prefixWord ++ tailWord_246083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246083).length < 2 ^ (prefixWord ++ tailWord_246083).sum := by decide
  have hdescent : baseEnd_246083 < baseStart_246083 := by decide
  rcases family_descends (prefixWord ++ tailWord_246083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246115 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 2, 5]
def baseStart_246115 : Nat := 118140960795 + 246115 * 2 ^ 59
def prefixEnd_246115 : Nat := 4983230072969 + 3 ^ 40 * 246115 * 2
def baseEnd_246115 : Nat := 84250194187606538420429

theorem tailTrace_246115 : CollatzResearch.WordTrace tailWord_246115 prefixEnd_246115 84250194187606538420429 := by
  unfold tailWord_246115
  simp only [CollatzResearch.WordTrace]
  refine ⟨8976551503374862940683799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5984367668916575293789199 8976551503374862940683799)
  ·
    refine ⟨13464827255062294411025699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8976551503374862940683799 13464827255062294411025699)
    ·
      refine ⟨20197240882593441616538549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13464827255062294411025699 20197240882593441616538549)
      ·
        refine ⟨1893491332743135151550489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20197240882593441616538549 1893491332743135151550489)
        ·
          refine ⟨1420118499557351363662867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1893491332743135151550489 1420118499557351363662867)
          ·
            refine ⟨2130177749336027045494301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420118499557351363662867 2130177749336027045494301)
            ·
              refine ⟨798816656001010142060363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2130177749336027045494301 798816656001010142060363)
              ·
                refine ⟨1198224984001515213090545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798816656001010142060363 1198224984001515213090545)
                ·
                  refine ⟨898668738001136409817909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1198224984001515213090545 898668738001136409817909)
                  ·
                    refine ⟨84250194187606538420429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 898668738001136409817909 84250194187606538420429)
                    ·
                      rfl

theorem cell22_246115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 5].length) (baseStart_246115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246115 prefixEnd_246115 := by exact prefixLift 246115
  have htrace : WordTrace (prefixWord ++ tailWord_246115) baseStart_246115 baseEnd_246115 := by
    simpa [prefixWord, tailWord_246115, baseEnd_246115] using wordTrace_append hprefix tailTrace_246115
  have hstable : (prefixWord ++ tailWord_246115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246115).length < 2 ^ (prefixWord ++ tailWord_246115).sum := by decide
  have hdescent : baseEnd_246115 < baseStart_246115 := by decide
  rcases family_descends (prefixWord ++ tailWord_246115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246175 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 3, 6]
def baseStart_246175 : Nat := 118140960795 + 246175 * 2 ^ 59
def prefixEnd_246175 : Nat := 4983230072969 + 3 ^ 40 * 246175 * 2
def baseEnd_246175 : Nat := 84270733413786381920245

theorem tailTrace_246175 : CollatzResearch.WordTrace tailWord_246175 prefixEnd_246175 84270733413786381920245 := by
  unfold tailWord_246175
  simp only [CollatzResearch.WordTrace]
  refine ⟨8978739883157493187867979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5985826588771662125245319 8978739883157493187867979)
  ·
    refine ⟨13468109824736239781801969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8978739883157493187867979 13468109824736239781801969)
    ·
      refine ⟨10101082368552179836351477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13468109824736239781801969 10101082368552179836351477)
      ·
        refine ⟨946976472051766859657951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10101082368552179836351477 946976472051766859657951)
        ·
          refine ⟨1420464708077650289486927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946976472051766859657951 1420464708077650289486927)
          ·
            refine ⟨2130697062116475434230391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420464708077650289486927 2130697062116475434230391)
            ·
              refine ⟨3196045593174713151345587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130697062116475434230391 3196045593174713151345587)
              ·
                refine ⟨4794068389762069727018381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3196045593174713151345587 4794068389762069727018381)
                ·
                  refine ⟨1797775646160776147631893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4794068389762069727018381 1797775646160776147631893)
                  ·
                    refine ⟨84270733413786381920245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1797775646160776147631893 84270733413786381920245)
                    ·
                      rfl

theorem cell22_246175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_246175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246175 prefixEnd_246175 := by exact prefixLift 246175
  have htrace : WordTrace (prefixWord ++ tailWord_246175) baseStart_246175 baseEnd_246175 := by
    simpa [prefixWord, tailWord_246175, baseEnd_246175] using wordTrace_append hprefix tailTrace_246175
  have hstable : (prefixWord ++ tailWord_246175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246175).length < 2 ^ (prefixWord ++ tailWord_246175).sum := by decide
  have hdescent : baseEnd_246175 < baseStart_246175 := by decide
  rcases family_descends (prefixWord ++ tailWord_246175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246228 : List Nat := [2, 4, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_246228 : Nat := 118140960795 + 246228 * 2 ^ 59
def prefixEnd_246228 : Nat := 4983230072969 + 3 ^ 40 * 246228 * 2
def baseEnd_246228 : Nat := 84288876396911910345083

theorem tailTrace_246228 : CollatzResearch.WordTrace tailWord_246228 prefixEnd_246228 84288876396911910345083 := by
  unfold tailWord_246228
  simp only [CollatzResearch.WordTrace]
  refine ⟨4490336475982741619773669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5987115301310322159698225 4490336475982741619773669)
  ·
    refine ⟨841938089246764053707563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4490336475982741619773669 841938089246764053707563)
    ·
      refine ⟨1262907133870146080561345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 841938089246764053707563 1262907133870146080561345)
      ·
        refine ⟨947180350402609560421009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1262907133870146080561345 947180350402609560421009)
        ·
          refine ⟨710385262801957170315757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 947180350402609560421009 710385262801957170315757)
          ·
            refine ⟨266394473550733938868409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 710385262801957170315757 266394473550733938868409)
            ·
              refine ⟨199795855163050454151307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266394473550733938868409 199795855163050454151307)
              ·
                refine ⟨299693782744575681226961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199795855163050454151307 299693782744575681226961)
                ·
                  refine ⟨224770337058431760920221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299693782744575681226961 224770337058431760920221)
                  ·
                    refine ⟨84288876396911910345083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224770337058431760920221 84288876396911910345083)
                    ·
                      rfl

theorem cell22_246228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_246228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246228 prefixEnd_246228 := by exact prefixLift 246228
  have htrace : WordTrace (prefixWord ++ tailWord_246228) baseStart_246228 baseEnd_246228 := by
    simpa [prefixWord, tailWord_246228, baseEnd_246228] using wordTrace_append hprefix tailTrace_246228
  have hstable : (prefixWord ++ tailWord_246228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246228).length < 2 ^ (prefixWord ++ tailWord_246228).sum := by decide
  have hdescent : baseEnd_246228 < baseStart_246228 := by decide
  rcases family_descends (prefixWord ++ tailWord_246228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246273 : List Nat := [1, 2, 4, 1, 3, 1, 4, 2, 1, 3]
def baseStart_246273 : Nat := 118140960795 + 246273 * 2 ^ 59
def prefixEnd_246273 : Nat := 4983230072969 + 3 ^ 40 * 246273 * 2
def baseEnd_246273 : Nat := 84304280816546792969945

theorem tailTrace_246273 : CollatzResearch.WordTrace tailWord_246273 prefixEnd_246273 84304280816546792969945 := by
  unfold tailWord_246273
  simp only [CollatzResearch.WordTrace]
  refine ⟨8982314236802455924935473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5988209491201637283290315 8982314236802455924935473)
  ·
    refine ⟨6736735677601841943701605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8982314236802455924935473 6736735677601841943701605)
    ·
      refine ⟨1263137939550345364444051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6736735677601841943701605 1263137939550345364444051)
      ·
        refine ⟨1894706909325518046666077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263137939550345364444051 1894706909325518046666077)
        ·
          refine ⟨710515090997069267499779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1894706909325518046666077 710515090997069267499779)
          ·
            refine ⟨1065772636495603901249669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710515090997069267499779 1065772636495603901249669)
            ·
              refine ⟨199832369342925731484313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1065772636495603901249669 199832369342925731484313)
              ·
                refine ⟨149874277007194298613235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199832369342925731484313 149874277007194298613235)
                ·
                  refine ⟨224811415510791447919853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149874277007194298613235 224811415510791447919853)
                  ·
                    refine ⟨84304280816546792969945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224811415510791447919853 84304280816546792969945)
                    ·
                      rfl

theorem cell22_246273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_246273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246273 prefixEnd_246273 := by exact prefixLift 246273
  have htrace : WordTrace (prefixWord ++ tailWord_246273) baseStart_246273 baseEnd_246273 := by
    simpa [prefixWord, tailWord_246273, baseEnd_246273] using wordTrace_append hprefix tailTrace_246273
  have hstable : (prefixWord ++ tailWord_246273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246273).length < 2 ^ (prefixWord ++ tailWord_246273).sum := by decide
  have hdescent : baseEnd_246273 < baseStart_246273 := by decide
  rcases family_descends (prefixWord ++ tailWord_246273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246282 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_246282 : Nat := 118140960795 + 246282 * 2 ^ 59
def prefixEnd_246282 : Nat := 4983230072969 + 3 ^ 40 * 246282 * 2
def baseEnd_246282 : Nat := 84307361700473769494917

theorem tailTrace_246282 : CollatzResearch.WordTrace tailWord_246282 prefixEnd_246282 84307361700473769494917 := by
  unfold tailWord_246282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2245660623442462615503275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5988428329179900308008733 2245660623442462615503275)
  ·
    refine ⟨3368490935163693923254913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2245660623442462615503275 3368490935163693923254913)
    ·
      refine ⟨2526368201372770442441185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3368490935163693923254913 2526368201372770442441185)
      ·
        refine ⟨1894776151029577831830889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2526368201372770442441185 1894776151029577831830889)
        ·
          refine ⟨1421082113272183373873167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1894776151029577831830889 1421082113272183373873167)
          ·
            refine ⟨2131623169908275060809751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421082113272183373873167 2131623169908275060809751)
            ·
              refine ⟨3197434754862412591214627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131623169908275060809751 3197434754862412591214627)
              ·
                refine ⟨4796152132293618886821941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3197434754862412591214627 4796152132293618886821941)
                ·
                  refine ⟨449639262402526770639557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4796152132293618886821941 449639262402526770639557)
                  ·
                    refine ⟨84307361700473769494917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 449639262402526770639557 84307361700473769494917)
                    ·
                      rfl

theorem cell22_246282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_246282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246282 prefixEnd_246282 := by exact prefixLift 246282
  have htrace : WordTrace (prefixWord ++ tailWord_246282) baseStart_246282 baseEnd_246282 := by
    simpa [prefixWord, tailWord_246282, baseEnd_246282] using wordTrace_append hprefix tailTrace_246282
  have hstable : (prefixWord ++ tailWord_246282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246282).length < 2 ^ (prefixWord ++ tailWord_246282).sum := by decide
  have hdescent : baseEnd_246282 < baseStart_246282 := by decide
  rcases family_descends (prefixWord ++ tailWord_246282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246327 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 4, 4]
def baseStart_246327 : Nat := 118140960795 + 246327 * 2 ^ 59
def prefixEnd_246327 : Nat := 4983230072969 + 3 ^ 40 * 246327 * 2
def baseEnd_246327 : Nat := 84322766120108652119779

theorem tailTrace_246327 : CollatzResearch.WordTrace tailWord_246327 prefixEnd_246327 84322766120108652119779 := by
  unfold tailWord_246327
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984283778606823147401235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5989522519071215431600823 8984283778606823147401235)
  ·
    refine ⟨13476425667910234721101853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8984283778606823147401235 13476425667910234721101853)
    ·
      refine ⟨5053659625466338020413195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13476425667910234721101853 5053659625466338020413195)
      ·
        refine ⟨7580489438199507030619793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5053659625466338020413195 7580489438199507030619793)
        ·
          refine ⟨5685367078649630272964845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7580489438199507030619793 5685367078649630272964845)
          ·
            refine ⟨2132012654493611352361817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5685367078649630272964845 2132012654493611352361817)
            ·
              refine ⟨1599009490870208514271363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2132012654493611352361817 1599009490870208514271363)
              ·
                refine ⟨2398514236305312771407045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599009490870208514271363 2398514236305312771407045)
                ·
                  refine ⟨449721419307246144638821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2398514236305312771407045 449721419307246144638821)
                  ·
                    refine ⟨84322766120108652119779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 449721419307246144638821 84322766120108652119779)
                    ·
                      rfl

theorem cell22_246327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_246327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246327 prefixEnd_246327 := by exact prefixLift 246327
  have htrace : WordTrace (prefixWord ++ tailWord_246327) baseStart_246327 baseEnd_246327 := by
    simpa [prefixWord, tailWord_246327, baseEnd_246327] using wordTrace_append hprefix tailTrace_246327
  have hstable : (prefixWord ++ tailWord_246327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246327).length < 2 ^ (prefixWord ++ tailWord_246327).sum := by decide
  have hdescent : baseEnd_246327 < baseStart_246327 := by decide
  rcases family_descends (prefixWord ++ tailWord_246327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246329 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 4, 3]
def baseStart_246329 : Nat := 118140960795 + 246329 * 2 ^ 59
def prefixEnd_246329 : Nat := 4983230072969 + 3 ^ 40 * 246329 * 2
def baseEnd_246329 : Nat := 84323450760981313569773

theorem tailTrace_246329 : CollatzResearch.WordTrace tailWord_246329 prefixEnd_246329 84323450760981313569773 := by
  unfold tailWord_246329
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984356724599577488974041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5989571149733051659316027 8984356724599577488974041)
  ·
    refine ⟨6738267543449683116730531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8984356724599577488974041 6738267543449683116730531)
    ·
      refine ⟨10107401315174524675095797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6738267543449683116730531 10107401315174524675095797)
      ·
        refine ⟨947568873297611688290231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10107401315174524675095797 947568873297611688290231)
        ·
          refine ⟨1421353309946417532435347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947568873297611688290231 1421353309946417532435347)
          ·
            refine ⟨2132029964919626298653021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421353309946417532435347 2132029964919626298653021)
            ·
              refine ⟨799511236844859861994883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2132029964919626298653021 799511236844859861994883)
              ·
                refine ⟨1199266855267289792992325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799511236844859861994883 1199266855267289792992325)
                ·
                  refine ⟨224862535362616836186061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199266855267289792992325 224862535362616836186061)
                  ·
                    refine ⟨84323450760981313569773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224862535362616836186061 84323450760981313569773)
                    ·
                      rfl

theorem cell22_246329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 3].length) (baseStart_246329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246329 prefixEnd_246329 := by exact prefixLift 246329
  have htrace : WordTrace (prefixWord ++ tailWord_246329) baseStart_246329 baseEnd_246329 := by
    simpa [prefixWord, tailWord_246329, baseEnd_246329] using wordTrace_append hprefix tailTrace_246329
  have hstable : (prefixWord ++ tailWord_246329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246329).length < 2 ^ (prefixWord ++ tailWord_246329).sum := by decide
  have hdescent : baseEnd_246329 < baseStart_246329 := by decide
  rcases family_descends (prefixWord ++ tailWord_246329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246376 : List Nat := [2, 1, 4, 3, 3, 1, 8]
def baseStart_246376 : Nat := 118140960795 + 246376 * 2 ^ 59
def prefixEnd_246376 : Nat := 4983230072969 + 3 ^ 40 * 246376 * 2
def baseEnd_246376 : Nat := 3123686660055142875727

theorem tailTrace_246376 : CollatzResearch.WordTrace tailWord_246376 prefixEnd_246376 3123686660055142875727 := by
  unfold tailWord_246376
  simp only [CollatzResearch.WordTrace]
  refine ⟨4493035477714652257967491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5990713970286203010623321 4493035477714652257967491)
  ·
    refine ⟨6739553216571978386951237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4493035477714652257967491 6739553216571978386951237)
    ·
      refine ⟨1263666228107245947553357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6739553216571978386951237 1263666228107245947553357)
      ·
        refine ⟨473874835540217230332509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1263666228107245947553357 473874835540217230332509)
        ·
          refine ⟨177703063327581461374691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473874835540217230332509 177703063327581461374691)
          ·
            refine ⟨266554594991372192062037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177703063327581461374691 266554594991372192062037)
            ·
              refine ⟨3123686660055142875727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 266554594991372192062037 3123686660055142875727)
              ·
                rfl

theorem cell22_246376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 8].length) (baseStart_246376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246376 prefixEnd_246376 := by exact prefixLift 246376
  have htrace : WordTrace (prefixWord ++ tailWord_246376) baseStart_246376 baseEnd_246376 := by
    simpa [prefixWord, tailWord_246376, baseEnd_246376] using wordTrace_append hprefix tailTrace_246376
  have hstable : (prefixWord ++ tailWord_246376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246376).length < 2 ^ (prefixWord ++ tailWord_246376).sum := by decide
  have hdescent : baseEnd_246376 < baseStart_246376 := by decide
  rcases family_descends (prefixWord ++ tailWord_246376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246391 : List Nat := [1, 1, 3, 1, 1, 3, 2, 6, 1, 3]
def baseStart_246391 : Nat := 118140960795 + 246391 * 2 ^ 59
def prefixEnd_246391 : Nat := 4983230072969 + 3 ^ 40 * 246391 * 2
def baseEnd_246391 : Nat := 84344674628033818519583

theorem tailTrace_246391 : CollatzResearch.WordTrace tailWord_246391 prefixEnd_246391 84344674628033818519583 := by
  unfold tailWord_246391
  simp only [CollatzResearch.WordTrace]
  refine ⟨8986618050374962077731027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5991078700249974718487351 8986618050374962077731027)
  ·
    refine ⟨13479927075562443116596541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8986618050374962077731027 13479927075562443116596541)
    ·
      refine ⟨5054972653335916168723703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13479927075562443116596541 5054972653335916168723703)
      ·
        refine ⟨7582458980003874253085555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5054972653335916168723703 7582458980003874253085555)
        ·
          refine ⟨11373688470005811379628333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7582458980003874253085555 11373688470005811379628333)
          ·
            refine ⟨4265133176252179267360625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11373688470005811379628333 4265133176252179267360625)
            ·
              refine ⟨3198849882189134450520469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4265133176252179267360625 3198849882189134450520469)
              ·
                refine ⟨149946088227615677368147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3198849882189134450520469 149946088227615677368147)
                ·
                  refine ⟨224919132341423516052221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149946088227615677368147 224919132341423516052221)
                  ·
                    refine ⟨84344674628033818519583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224919132341423516052221 84344674628033818519583)
                    ·
                      rfl

theorem cell22_246391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_246391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246391 prefixEnd_246391 := by exact prefixLift 246391
  have htrace : WordTrace (prefixWord ++ tailWord_246391) baseStart_246391 baseEnd_246391 := by
    simpa [prefixWord, tailWord_246391, baseEnd_246391] using wordTrace_append hprefix tailTrace_246391
  have hstable : (prefixWord ++ tailWord_246391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246391).length < 2 ^ (prefixWord ++ tailWord_246391).sum := by decide
  have hdescent : baseEnd_246391 < baseStart_246391 := by decide
  rcases family_descends (prefixWord ++ tailWord_246391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246442 : List Nat := [3, 1, 5, 2, 1, 1, 1, 4, 1, 3]
def baseStart_246442 : Nat := 118140960795 + 246442 * 2 ^ 59
def prefixEnd_246442 : Nat := 4983230072969 + 3 ^ 40 * 246442 * 2
def baseEnd_246442 : Nat := 84362132970286685494427

theorem tailTrace_246442 : CollatzResearch.WordTrace tailWord_246442 prefixEnd_246442 84362132970286685494427 := by
  unfold tailWord_246442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247119543297549446959395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5992318782126798525225053 2247119543297549446959395)
  ·
    refine ⟨3370679314946324170439093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2247119543297549446959395 3370679314946324170439093)
    ·
      refine ⟨316001185776217890978665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3370679314946324170439093 316001185776217890978665)
      ·
        refine ⟨237000889332163418233999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316001185776217890978665 237000889332163418233999)
        ·
          refine ⟨355501333998245127350999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237000889332163418233999 355501333998245127350999)
          ·
            refine ⟨533252000997367691026499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355501333998245127350999 533252000997367691026499)
            ·
              refine ⟨799878001496051536539749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533252000997367691026499 799878001496051536539749)
              ·
                refine ⟨149977125280509663101203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 799878001496051536539749 149977125280509663101203)
                ·
                  refine ⟨224965687920764494651805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149977125280509663101203 224965687920764494651805)
                  ·
                    refine ⟨84362132970286685494427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224965687920764494651805 84362132970286685494427)
                    ·
                      rfl

theorem cell22_246442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_246442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246442 prefixEnd_246442 := by exact prefixLift 246442
  have htrace : WordTrace (prefixWord ++ tailWord_246442) baseStart_246442 baseEnd_246442 := by
    simpa [prefixWord, tailWord_246442, baseEnd_246442] using wordTrace_append hprefix tailTrace_246442
  have hstable : (prefixWord ++ tailWord_246442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246442).length < 2 ^ (prefixWord ++ tailWord_246442).sum := by decide
  have hdescent : baseEnd_246442 < baseStart_246442 := by decide
  rcases family_descends (prefixWord ++ tailWord_246442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246464 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 1, 5]
def baseStart_246464 : Nat := 118140960795 + 246464 * 2 ^ 59
def prefixEnd_246464 : Nat := 4983230072969 + 3 ^ 40 * 246464 * 2
def baseEnd_246464 : Nat := 84369664019885961444359

theorem tailTrace_246464 : CollatzResearch.WordTrace tailWord_246464 prefixEnd_246464 84369664019885961444359 := by
  unfold tailWord_246464
  simp only [CollatzResearch.WordTrace]
  refine ⟨4494640289555247772569223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5992853719406997030092297 4494640289555247772569223)
  ·
    refine ⟨6741960434332871658853835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4494640289555247772569223 6741960434332871658853835)
    ·
      refine ⟨10112940651499307488280753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6741960434332871658853835 10112940651499307488280753)
      ·
        refine ⟨7584705488624480616210565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10112940651499307488280753 7584705488624480616210565)
        ·
          refine ⟨1422132279117090115539481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7584705488624480616210565 1422132279117090115539481)
          ·
            refine ⟨1066599209337817586654611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1422132279117090115539481 1066599209337817586654611)
            ·
              refine ⟨1599898814006726379981917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066599209337817586654611 1599898814006726379981917)
              ·
                refine ⟨599962055252522392493219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1599898814006726379981917 599962055252522392493219)
                ·
                  refine ⟨899943082878783588739829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599962055252522392493219 899943082878783588739829)
                  ·
                    refine ⟨84369664019885961444359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 899943082878783588739829 84369664019885961444359)
                    ·
                      rfl

theorem cell22_246464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_246464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246464 prefixEnd_246464 := by exact prefixLift 246464
  have htrace : WordTrace (prefixWord ++ tailWord_246464) baseStart_246464 baseEnd_246464 := by
    simpa [prefixWord, tailWord_246464, baseEnd_246464] using wordTrace_append hprefix tailTrace_246464
  have hstable : (prefixWord ++ tailWord_246464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246464).length < 2 ^ (prefixWord ++ tailWord_246464).sum := by decide
  have hdescent : baseEnd_246464 < baseStart_246464 := by decide
  rcases family_descends (prefixWord ++ tailWord_246464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246569 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 5, 4]
def baseStart_246569 : Nat := 118140960795 + 246569 * 2 ^ 59
def prefixEnd_246569 : Nat := 4983230072969 + 3 ^ 40 * 246569 * 2
def baseEnd_246569 : Nat := 84405607665700687569037

theorem tailTrace_246569 : CollatzResearch.WordTrace tailWord_246569 prefixEnd_246569 84405607665700687569037 := by
  unfold tailWord_246569
  simp only [CollatzResearch.WordTrace]
  refine ⟨8993110243730098477710761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5995406829153398985140507 8993110243730098477710761)
  ·
    refine ⟨6744832682797573858283071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8993110243730098477710761 6744832682797573858283071)
    ·
      refine ⟨10117249024196360787424607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6744832682797573858283071 10117249024196360787424607)
      ·
        refine ⟨15175873536294541181136911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10117249024196360787424607 15175873536294541181136911)
        ·
          refine ⟨22763810304441811771705367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15175873536294541181136911 22763810304441811771705367)
          ·
            refine ⟨34145715456662717657558051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22763810304441811771705367 34145715456662717657558051)
            ·
              refine ⟨51218573184994076486337077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34145715456662717657558051 51218573184994076486337077)
              ·
                refine ⟨4801741236093194670594101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51218573184994076486337077 4801741236093194670594101)
                ·
                  refine ⟨450163240883737000368197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4801741236093194670594101 450163240883737000368197)
                  ·
                    refine ⟨84405607665700687569037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 450163240883737000368197 84405607665700687569037)
                    ·
                      rfl

theorem cell22_246569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_246569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246569 prefixEnd_246569 := by exact prefixLift 246569
  have htrace : WordTrace (prefixWord ++ tailWord_246569) baseStart_246569 baseEnd_246569 := by
    simpa [prefixWord, tailWord_246569, baseEnd_246569] using wordTrace_append hprefix tailTrace_246569
  have hstable : (prefixWord ++ tailWord_246569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246569).length < 2 ^ (prefixWord ++ tailWord_246569).sum := by decide
  have hdescent : baseEnd_246569 < baseStart_246569 := by decide
  rcases family_descends (prefixWord ++ tailWord_246569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246584 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 8]
def baseStart_246584 : Nat := 118140960795 + 246584 * 2 ^ 59
def prefixEnd_246584 : Nat := 4983230072969 + 3 ^ 40 * 246584 * 2
def baseEnd_246584 : Nat := 28136914157415216147997

theorem tailTrace_246584 : CollatzResearch.WordTrace tailWord_246584 prefixEnd_246584 28136914157415216147997 := by
  unfold tailWord_246584
  simp only [CollatzResearch.WordTrace]
  refine ⟨4496828669337878019753403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5995771559117170693004537 4496828669337878019753403)
  ·
    refine ⟨6745243004006817029630105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4496828669337878019753403 6745243004006817029630105)
    ·
      refine ⟨5058932253005112772222579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6745243004006817029630105 5058932253005112772222579)
      ·
        refine ⟨7588398379507669158333869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5058932253005112772222579 7588398379507669158333869)
        ·
          refine ⟨2845649392315375934375201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7588398379507669158333869 2845649392315375934375201)
          ·
            refine ⟨2134237044236531950781401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845649392315375934375201 2134237044236531950781401)
            ·
              refine ⟨1600677783177398963086051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2134237044236531950781401 1600677783177398963086051)
              ·
                refine ⟨2401016674766098444629077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600677783177398963086051 2401016674766098444629077)
                ·
                  refine ⟨28136914157415216147997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2401016674766098444629077 28136914157415216147997)
                  ·
                    rfl

theorem cell22_246584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_246584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246584 prefixEnd_246584 := by exact prefixLift 246584
  have htrace : WordTrace (prefixWord ++ tailWord_246584) baseStart_246584 baseEnd_246584 := by
    simpa [prefixWord, tailWord_246584, baseEnd_246584] using wordTrace_append hprefix tailTrace_246584
  have hstable : (prefixWord ++ tailWord_246584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246584).length < 2 ^ (prefixWord ++ tailWord_246584).sum := by decide
  have hdescent : baseEnd_246584 < baseStart_246584 := by decide
  rcases family_descends (prefixWord ++ tailWord_246584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246616 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 4, 3]
def baseStart_246616 : Nat := 118140960795 + 246616 * 2 ^ 59
def prefixEnd_246616 : Nat := 4983230072969 + 3 ^ 40 * 246616 * 2
def baseEnd_246616 : Nat := 84421696726208231643893

theorem tailTrace_246616 : CollatzResearch.WordTrace tailWord_246616 prefixEnd_246616 84421696726208231643893 := by
  unfold tailWord_246616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4497412237279912752335851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5996549649706550336447801 4497412237279912752335851)
  ·
    refine ⟨6746118355919869128503777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4497412237279912752335851 6746118355919869128503777)
    ·
      refine ⟨5059588766939901846377833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6746118355919869128503777 5059588766939901846377833)
      ·
        refine ⟨3794691575204926384783375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5059588766939901846377833 3794691575204926384783375)
        ·
          refine ⟨5692037362807389577175063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3794691575204926384783375 5692037362807389577175063)
          ·
            refine ⟨8538056044211084365762595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5692037362807389577175063 8538056044211084365762595)
            ·
              refine ⟨12807084066316626548643893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8538056044211084365762595 12807084066316626548643893)
              ·
                refine ⟨1200664131217183738935365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12807084066316626548643893 1200664131217183738935365)
                ·
                  refine ⟨225124524603221951050381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1200664131217183738935365 225124524603221951050381)
                  ·
                    refine ⟨84421696726208231643893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225124524603221951050381 84421696726208231643893)
                    ·
                      rfl

theorem cell22_246616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_246616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246616 prefixEnd_246616 := by exact prefixLift 246616
  have htrace : WordTrace (prefixWord ++ tailWord_246616) baseStart_246616 baseEnd_246616 := by
    simpa [prefixWord, tailWord_246616, baseEnd_246616] using wordTrace_append hprefix tailTrace_246616
  have hstable : (prefixWord ++ tailWord_246616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246616).length < 2 ^ (prefixWord ++ tailWord_246616).sum := by decide
  have hdescent : baseEnd_246616 < baseStart_246616 := by decide
  rcases family_descends (prefixWord ++ tailWord_246616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246618 : List Nat := [3, 1, 1, 2, 1, 5, 1, 4, 4]
def baseStart_246618 : Nat := 118140960795 + 246618 * 2 ^ 59
def prefixEnd_246618 : Nat := 4983230072969 + 3 ^ 40 * 246618 * 2
def baseEnd_246618 : Nat := 28140793789026964364629

theorem tailTrace_246618 : CollatzResearch.WordTrace tailWord_246618 prefixEnd_246618 28140793789026964364629 := by
  unfold tailWord_246618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2248724355138144961561127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5996598280368386564163005 2248724355138144961561127)
  ·
    refine ⟨3373086532707217442341691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2248724355138144961561127 3373086532707217442341691)
    ·
      refine ⟨5059629799060826163512537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3373086532707217442341691 5059629799060826163512537)
      ·
        refine ⟨3794722349295619622634403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5059629799060826163512537 3794722349295619622634403)
        ·
          refine ⟨5692083523943429433951605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3794722349295619622634403 5692083523943429433951605)
          ·
            refine ⟨533632830369696509432963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5692083523943429433951605 533632830369696509432963)
            ·
              refine ⟨800449245554544764149445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533632830369696509432963 800449245554544764149445)
              ·
                refine ⟨150084233541477143278021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 800449245554544764149445 150084233541477143278021)
                ·
                  refine ⟨28140793789026964364629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150084233541477143278021 28140793789026964364629)
                  ·
                    rfl

theorem cell22_246618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_246618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246618 prefixEnd_246618 := by exact prefixLift 246618
  have htrace : WordTrace (prefixWord ++ tailWord_246618) baseStart_246618 baseEnd_246618 := by
    simpa [prefixWord, tailWord_246618, baseEnd_246618] using wordTrace_append hprefix tailTrace_246618
  have hstable : (prefixWord ++ tailWord_246618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246618).length < 2 ^ (prefixWord ++ tailWord_246618).sum := by decide
  have hdescent : baseEnd_246618 < baseStart_246618 := by decide
  rcases family_descends (prefixWord ++ tailWord_246618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246654 : List Nat := [4, 2, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_246654 : Nat := 118140960795 + 246654 * 2 ^ 59
def prefixEnd_246654 : Nat := 4983230072969 + 3 ^ 40 * 246654 * 2
def baseEnd_246654 : Nat := 84434704902788799193777

theorem tailTrace_246654 : CollatzResearch.WordTrace tailWord_246654 prefixEnd_246654 84434704902788799193777 := by
  unfold tailWord_246654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124526306052769749319377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5997473632281438663036677 1124526306052769749319377)
  ·
    refine ⟨843394729539577311989533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1124526306052769749319377 843394729539577311989533)
    ·
      refine ⟨316273023577341491996075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 843394729539577311989533 316273023577341491996075)
      ·
        refine ⟨474409535366012237994113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316273023577341491996075 474409535366012237994113)
        ·
          refine ⟨355807151524509178495585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474409535366012237994113 355807151524509178495585)
          ·
            refine ⟨266855363643381883871689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355807151524509178495585 266855363643381883871689)
            ·
              refine ⟨200141522732536412903767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266855363643381883871689 200141522732536412903767)
              ·
                refine ⟨300212284098804619355651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200141522732536412903767 300212284098804619355651)
                ·
                  refine ⟨450318426148206929033477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300212284098804619355651 450318426148206929033477)
                  ·
                    refine ⟨84434704902788799193777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 450318426148206929033477 84434704902788799193777)
                    ·
                      rfl

theorem cell22_246654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_246654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246654 prefixEnd_246654 := by exact prefixLift 246654
  have htrace : WordTrace (prefixWord ++ tailWord_246654) baseStart_246654 baseEnd_246654 := by
    simpa [prefixWord, tailWord_246654, baseEnd_246654] using wordTrace_append hprefix tailTrace_246654
  have hstable : (prefixWord ++ tailWord_246654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246654).length < 2 ^ (prefixWord ++ tailWord_246654).sum := by decide
  have hdescent : baseEnd_246654 < baseStart_246654 := by decide
  rcases family_descends (prefixWord ++ tailWord_246654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246691 : List Nat := [1, 1, 1, 4, 1, 2, 2, 5, 5]
def baseStart_246691 : Nat := 118140960795 + 246691 * 2 ^ 59
def prefixEnd_246691 : Nat := 4983230072969 + 3 ^ 40 * 246691 * 2
def baseEnd_246691 : Nat := 28149123586311012006221

theorem tailTrace_246691 : CollatzResearch.WordTrace tailWord_246691 prefixEnd_246691 28149123586311012006221 := by
  unfold tailWord_246691
  simp only [CollatzResearch.WordTrace]
  refine ⟨8997559949288113313651927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5998373299525408875767951 8997559949288113313651927)
  ·
    refine ⟨13496339923932169970477891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8997559949288113313651927 13496339923932169970477891)
    ·
      refine ⟨20244509885898254955716837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13496339923932169970477891 20244509885898254955716837)
      ·
        refine ⟨3795845603605922804196907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20244509885898254955716837 3795845603605922804196907)
        ·
          refine ⟨5693768405408884206295361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3795845603605922804196907 5693768405408884206295361)
          ·
            refine ⟨4270326304056663154721521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5693768405408884206295361 4270326304056663154721521)
            ·
              refine ⟨3202744728042497366041141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4270326304056663154721521 3202744728042497366041141)
              ·
                refine ⟨300257318253984128066357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3202744728042497366041141 300257318253984128066357)
                ·
                  refine ⟨28149123586311012006221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300257318253984128066357 28149123586311012006221)
                  ·
                    rfl

theorem cell22_246691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 5].length) (baseStart_246691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246691 prefixEnd_246691 := by exact prefixLift 246691
  have htrace : WordTrace (prefixWord ++ tailWord_246691) baseStart_246691 baseEnd_246691 := by
    simpa [prefixWord, tailWord_246691, baseEnd_246691] using wordTrace_append hprefix tailTrace_246691
  have hstable : (prefixWord ++ tailWord_246691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246691).length < 2 ^ (prefixWord ++ tailWord_246691).sum := by decide
  have hdescent : baseEnd_246691 < baseStart_246691 := by decide
  rcases family_descends (prefixWord ++ tailWord_246691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246712 : List Nat := [2, 1, 2, 1, 2, 6, 1, 3, 1, 3]
def baseStart_246712 : Nat := 118140960795 + 246712 * 2 ^ 59
def prefixEnd_246712 : Nat := 4983230072969 + 3 ^ 40 * 246712 * 2
def baseEnd_246712 : Nat := 84454559488095981243599

theorem tailTrace_246712 : CollatzResearch.WordTrace tailWord_246712 prefixEnd_246712 84454559488095981243599 := by
  unfold tailWord_246712
  simp only [CollatzResearch.WordTrace]
  refine ⟨4499162941106016950083195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5998883921474689266777593 4499162941106016950083195)
  ·
    refine ⟨6748744411659025425124793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4499162941106016950083195 6748744411659025425124793)
    ·
      refine ⟨5061558308744269068843595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6748744411659025425124793 5061558308744269068843595)
      ·
        refine ⟨7592337463116403603265393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5061558308744269068843595 7592337463116403603265393)
        ·
          refine ⟨5694253097337302702449045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7592337463116403603265393 5694253097337302702449045)
          ·
            refine ⟨266918113937686064177299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5694253097337302702449045 266918113937686064177299)
            ·
              refine ⟨400377170906529096265949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266918113937686064177299 400377170906529096265949)
              ·
                refine ⟨150141439089948411099731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400377170906529096265949 150141439089948411099731)
                ·
                  refine ⟨225212158634922616649597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150141439089948411099731 225212158634922616649597)
                  ·
                    refine ⟨84454559488095981243599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225212158634922616649597 84454559488095981243599)
                    ·
                      rfl

theorem cell22_246712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_246712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246712 prefixEnd_246712 := by exact prefixLift 246712
  have htrace : WordTrace (prefixWord ++ tailWord_246712) baseStart_246712 baseEnd_246712 := by
    simpa [prefixWord, tailWord_246712, baseEnd_246712] using wordTrace_append hprefix tailTrace_246712
  have hstable : (prefixWord ++ tailWord_246712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246712).length < 2 ^ (prefixWord ++ tailWord_246712).sum := by decide
  have hdescent : baseEnd_246712 < baseStart_246712 := by decide
  rcases family_descends (prefixWord ++ tailWord_246712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246742 : List Nat := [5, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_246742 : Nat := 118140960795 + 246742 * 2 ^ 59
def prefixEnd_246742 : Nat := 4983230072969 + 3 ^ 40 * 246742 * 2
def baseEnd_246742 : Nat := 28154943033728634331169

theorem tailTrace_246742 : CollatzResearch.WordTrace tailWord_246742 prefixEnd_246742 28154943033728634331169 := by
  unfold tailWord_246742
  simp only [CollatzResearch.WordTrace]
  refine ⟨562463754506459313984905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5999613381402232682505653 562463754506459313984905)
  ·
    refine ⟨421847815879844485488679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 562463754506459313984905 421847815879844485488679)
    ·
      refine ⟨632771723819766728233019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421847815879844485488679 632771723819766728233019)
      ·
        refine ⟨949157585729650092349529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632771723819766728233019 949157585729650092349529)
        ·
          refine ⟨711868189297237569262147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 949157585729650092349529 711868189297237569262147)
          ·
            refine ⟨1067802283945856353893221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711868189297237569262147 1067802283945856353893221)
            ·
              refine ⟨200212928239848066354979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1067802283945856353893221 200212928239848066354979)
              ·
                refine ⟨300319392359772099532469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200212928239848066354979 300319392359772099532469)
                ·
                  refine ⟨28154943033728634331169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300319392359772099532469 28154943033728634331169)
                  ·
                    rfl

theorem cell22_246742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_246742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246742 prefixEnd_246742 := by exact prefixLift 246742
  have htrace : WordTrace (prefixWord ++ tailWord_246742) baseStart_246742 baseEnd_246742 := by
    simpa [prefixWord, tailWord_246742, baseEnd_246742] using wordTrace_append hprefix tailTrace_246742
  have hstable : (prefixWord ++ tailWord_246742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246742).length < 2 ^ (prefixWord ++ tailWord_246742).sum := by decide
  have hdescent : baseEnd_246742 < baseStart_246742 := by decide
  rcases family_descends (prefixWord ++ tailWord_246742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246785 : List Nat := [1, 2, 4, 1, 2, 2, 1, 4, 2, 3]
def baseStart_246785 : Nat := 118140960795 + 246785 * 2 ^ 59
def prefixEnd_246785 : Nat := 4983230072969 + 3 ^ 40 * 246785 * 2
def baseEnd_246785 : Nat := 84479548879948124168375

theorem tailTrace_246785 : CollatzResearch.WordTrace tailWord_246785 prefixEnd_246785 84479548879948124168375 := by
  unfold tailWord_246785
  simp only [CollatzResearch.WordTrace]
  refine ⟨9000988410947567367573809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6000658940631711578382539 9000988410947567367573809)
  ·
    refine ⟨6750741308210675525680357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9000988410947567367573809 6750741308210675525680357)
    ·
      refine ⟨1265763995289501661065067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6750741308210675525680357 1265763995289501661065067)
      ·
        refine ⟨1898645992934252491597601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265763995289501661065067 1898645992934252491597601)
        ·
          refine ⟨1423984494700689368698201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1898645992934252491597601 1423984494700689368698201)
          ·
            refine ⟨1067988371025517026523651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423984494700689368698201 1067988371025517026523651)
            ·
              refine ⟨1601982556538275539785477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067988371025517026523651 1601982556538275539785477)
              ·
                refine ⟨300371729350926663709777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1601982556538275539785477 300371729350926663709777)
                ·
                  refine ⟨225278797013194997782333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300371729350926663709777 225278797013194997782333)
                  ·
                    refine ⟨84479548879948124168375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225278797013194997782333 84479548879948124168375)
                    ·
                      rfl

theorem cell22_246785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_246785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246785 prefixEnd_246785 := by exact prefixLift 246785
  have htrace : WordTrace (prefixWord ++ tailWord_246785) baseStart_246785 baseEnd_246785 := by
    simpa [prefixWord, tailWord_246785, baseEnd_246785] using wordTrace_append hprefix tailTrace_246785
  have hstable : (prefixWord ++ tailWord_246785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246785).length < 2 ^ (prefixWord ++ tailWord_246785).sum := by decide
  have hdescent : baseEnd_246785 < baseStart_246785 := by decide
  rcases family_descends (prefixWord ++ tailWord_246785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246798 : List Nat := [4, 1, 1, 2, 2, 2, 3, 7]
def baseStart_246798 : Nat := 118140960795 + 246798 * 2 ^ 59
def prefixEnd_246798 : Nat := 4983230072969 + 3 ^ 40 * 246798 * 2
def baseEnd_246798 : Nat := 9387111005068935954815

theorem tailTrace_246798 : CollatzResearch.WordTrace tailWord_246798 prefixEnd_246798 9387111005068935954815 := by
  unfold tailWord_246798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1125182819987558823474631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6000975039933647058531365 1125182819987558823474631)
  ·
    refine ⟨1687774229981338235211947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1125182819987558823474631 1687774229981338235211947)
    ·
      refine ⟨2531661344972007352817921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1687774229981338235211947 2531661344972007352817921)
      ·
        refine ⟨1898746008729005514613441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2531661344972007352817921 1898746008729005514613441)
        ·
          refine ⟨1424059506546754135960081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1898746008729005514613441 1424059506546754135960081)
          ·
            refine ⟨1068044629910065601970061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1424059506546754135960081 1068044629910065601970061)
            ·
              refine ⟨400516736216274600738773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1068044629910065601970061 400516736216274600738773)
              ·
                refine ⟨9387111005068935954815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 400516736216274600738773 9387111005068935954815)
                ·
                  rfl

theorem cell22_246798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_246798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246798 prefixEnd_246798 := by exact prefixLift 246798
  have htrace : WordTrace (prefixWord ++ tailWord_246798) baseStart_246798 baseEnd_246798 := by
    simpa [prefixWord, tailWord_246798, baseEnd_246798] using wordTrace_append hprefix tailTrace_246798
  have hstable : (prefixWord ++ tailWord_246798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246798).length < 2 ^ (prefixWord ++ tailWord_246798).sum := by decide
  have hdescent : baseEnd_246798 < baseStart_246798 := by decide
  rcases family_descends (prefixWord ++ tailWord_246798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246830 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_246830 : Nat := 118140960795 + 246830 * 2 ^ 59
def prefixEnd_246830 : Nat := 4983230072969 + 3 ^ 40 * 246830 * 2
def baseEnd_246830 : Nat := 84494953299583006793237

theorem tailTrace_246830 : CollatzResearch.WordTrace tailWord_246830 prefixEnd_246830 84494953299583006793237 := by
  unfold tailWord_246830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1125328711973067506620243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6001753130523026701974629 1125328711973067506620243)
  ·
    refine ⟨1687993067959601259930365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1125328711973067506620243 1687993067959601259930365)
    ·
      refine ⟨632997400484850472473887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1687993067959601259930365 632997400484850472473887)
      ·
        refine ⟨949496100727275708710831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632997400484850472473887 949496100727275708710831)
        ·
          refine ⟨1424244151090913563066247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949496100727275708710831 1424244151090913563066247)
          ·
            refine ⟨2136366226636370344599371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424244151090913563066247 2136366226636370344599371)
            ·
              refine ⟨3204549339954555516899057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136366226636370344599371 3204549339954555516899057)
              ·
                refine ⟨2403412004965916637674293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3204549339954555516899057 2403412004965916637674293)
                ·
                  refine ⟨225319875465554684781965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2403412004965916637674293 225319875465554684781965)
                  ·
                    refine ⟨84494953299583006793237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225319875465554684781965 84494953299583006793237)
                    ·
                      rfl

theorem cell22_246830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_246830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246830 prefixEnd_246830 := by exact prefixLift 246830
  have htrace : WordTrace (prefixWord ++ tailWord_246830) baseStart_246830 baseEnd_246830 := by
    simpa [prefixWord, tailWord_246830, baseEnd_246830] using wordTrace_append hprefix tailTrace_246830
  have hstable : (prefixWord ++ tailWord_246830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246830).length < 2 ^ (prefixWord ++ tailWord_246830).sum := by decide
  have hdescent : baseEnd_246830 < baseStart_246830 := by decide
  rcases family_descends (prefixWord ++ tailWord_246830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246858 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_246858 : Nat := 118140960795 + 246858 * 2 ^ 59
def prefixEnd_246858 : Nat := 4983230072969 + 3 ^ 40 * 246858 * 2
def baseEnd_246858 : Nat := 84504538271800267093151

theorem tailTrace_246858 : CollatzResearch.WordTrace tailWord_246858 prefixEnd_246858 84504538271800267093151 := by
  unfold tailWord_246858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2250912734920775208745307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6002433959788733889987485 2250912734920775208745307)
  ·
    refine ⟨3376369102381162813117961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2250912734920775208745307 3376369102381162813117961)
    ·
      refine ⟨2532276826785872109838471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3376369102381162813117961 2532276826785872109838471)
      ·
        refine ⟨3798415240178808164757707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2532276826785872109838471 3798415240178808164757707)
        ·
          refine ⟨5697622860268212247136561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3798415240178808164757707 5697622860268212247136561)
          ·
            refine ⟨4273217145201159185352421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5697622860268212247136561 4273217145201159185352421)
            ·
              refine ⟨801228214725217347253579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4273217145201159185352421 801228214725217347253579)
              ·
                refine ⟨1201842322087826020880369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801228214725217347253579 1201842322087826020880369)
                ·
                  refine ⟨901381741565869515660277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1201842322087826020880369 901381741565869515660277)
                  ·
                    refine ⟨84504538271800267093151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 901381741565869515660277 84504538271800267093151)
                    ·
                      rfl

theorem cell22_246858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_246858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246858 prefixEnd_246858 := by exact prefixLift 246858
  have htrace : WordTrace (prefixWord ++ tailWord_246858) baseStart_246858 baseEnd_246858 := by
    simpa [prefixWord, tailWord_246858, baseEnd_246858] using wordTrace_append hprefix tailTrace_246858
  have hstable : (prefixWord ++ tailWord_246858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246858).length < 2 ^ (prefixWord ++ tailWord_246858).sum := by decide
  have hdescent : baseEnd_246858 < baseStart_246858 := by decide
  rcases family_descends (prefixWord ++ tailWord_246858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246935 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 2, 4]
def baseStart_246935 : Nat := 118140960795 + 246935 * 2 ^ 59
def prefixEnd_246935 : Nat := 4983230072969 + 3 ^ 40 * 246935 * 2
def baseEnd_246935 : Nat := 84530896945397732917915

theorem tailTrace_246935 : CollatzResearch.WordTrace tailWord_246935 prefixEnd_246935 84530896945397732917915 := by
  unfold tailWord_246935
  simp only [CollatzResearch.WordTrace]
  refine ⟨9006459360404142985534259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6004306240269428657022839 9006459360404142985534259)
  ·
    refine ⟨13509689040606214478301389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9006459360404142985534259 13509689040606214478301389)
    ·
      refine ⟨5066133390227330429363021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13509689040606214478301389 5066133390227330429363021)
      ·
        refine ⟨1899800021335248911011133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5066133390227330429363021 1899800021335248911011133)
        ·
          refine ⟨712425008000718341629175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1899800021335248911011133 712425008000718341629175)
          ·
            refine ⟨1068637512001077512443763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712425008000718341629175 1068637512001077512443763)
            ·
              refine ⟨1602956268001616268665645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068637512001077512443763 1602956268001616268665645)
              ·
                refine ⟨601108600500606100749617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1602956268001616268665645 601108600500606100749617)
                ·
                  refine ⟨450831450375454575562213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601108600500606100749617 450831450375454575562213)
                  ·
                    refine ⟨84530896945397732917915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 450831450375454575562213 84530896945397732917915)
                    ·
                      rfl

theorem cell22_246935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_246935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246935 prefixEnd_246935 := by exact prefixLift 246935
  have htrace : WordTrace (prefixWord ++ tailWord_246935) baseStart_246935 baseEnd_246935 := by
    simpa [prefixWord, tailWord_246935, baseEnd_246935] using wordTrace_append hprefix tailTrace_246935
  have hstable : (prefixWord ++ tailWord_246935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246935).length < 2 ^ (prefixWord ++ tailWord_246935).sum := by decide
  have hdescent : baseEnd_246935 < baseStart_246935 := by decide
  rcases family_descends (prefixWord ++ tailWord_246935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246954 : List Nat := [3, 1, 5, 1, 1, 1, 1, 4, 2, 3]
def baseStart_246954 : Nat := 118140960795 + 246954 * 2 ^ 59
def prefixEnd_246954 : Nat := 4983230072969 + 3 ^ 40 * 246954 * 2
def baseEnd_246954 : Nat := 84537401033688016692857

theorem tailTrace_246954 : CollatzResearch.WordTrace tailWord_246954 prefixEnd_246954 84537401033688016692857 := by
  unfold tailWord_246954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2251788086833827307618979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6004768231556872820317277 2251788086833827307618979)
  ·
    refine ⟨3377682130250740961428469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2251788086833827307618979 3377682130250740961428469)
    ·
      refine ⟨316657699711006965133919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3377682130250740961428469 316657699711006965133919)
      ·
        refine ⟨474986549566510447700879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316657699711006965133919 474986549566510447700879)
        ·
          refine ⟨712479824349765671551319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474986549566510447700879 712479824349765671551319)
          ·
            refine ⟨1068719736524648507326979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712479824349765671551319 1068719736524648507326979)
            ·
              refine ⟨1603079604786972760990469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068719736524648507326979 1603079604786972760990469)
              ·
                refine ⟨300577425897557392685713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1603079604786972760990469 300577425897557392685713)
                ·
                  refine ⟨225433069423168044514285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300577425897557392685713 225433069423168044514285)
                  ·
                    refine ⟨84537401033688016692857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225433069423168044514285 84537401033688016692857)
                    ·
                      rfl

theorem cell22_246954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_246954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246954 prefixEnd_246954 := by exact prefixLift 246954
  have htrace : WordTrace (prefixWord ++ tailWord_246954) baseStart_246954 baseEnd_246954 := by
    simpa [prefixWord, tailWord_246954, baseEnd_246954] using wordTrace_append hprefix tailTrace_246954
  have hstable : (prefixWord ++ tailWord_246954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246954).length < 2 ^ (prefixWord ++ tailWord_246954).sum := by decide
  have hdescent : baseEnd_246954 < baseStart_246954 := by decide
  rcases family_descends (prefixWord ++ tailWord_246954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246963 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 2, 6]
def baseStart_246963 : Nat := 118140960795 + 246963 * 2 ^ 59
def prefixEnd_246963 : Nat := 4983230072969 + 3 ^ 40 * 246963 * 2
def baseEnd_246963 : Nat := 84540481917614993217829

theorem tailTrace_246963 : CollatzResearch.WordTrace tailWord_246963 prefixEnd_246963 84540481917614993217829 := by
  unfold tailWord_246963
  simp only [CollatzResearch.WordTrace]
  refine ⟨9007480604302703767553543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6004987069535135845035695 9007480604302703767553543)
  ·
    refine ⟨13511220906454055651330315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9007480604302703767553543 13511220906454055651330315)
    ·
      refine ⟨20266831359681083476995473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13511220906454055651330315 20266831359681083476995473)
      ·
        refine ⟨15200123519760812607746605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20266831359681083476995473 15200123519760812607746605)
        ·
          refine ⟨5700046319910304727904977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15200123519760812607746605 5700046319910304727904977)
          ·
            refine ⟨4275034739932728545928733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5700046319910304727904977 4275034739932728545928733)
            ·
              refine ⟨1603138027474773204723275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4275034739932728545928733 1603138027474773204723275)
              ·
                refine ⟨2404707041212159807084913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603138027474773204723275 2404707041212159807084913)
                ·
                  refine ⟨1803530280909119855313685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2404707041212159807084913 1803530280909119855313685)
                  ·
                    refine ⟨84540481917614993217829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1803530280909119855313685 84540481917614993217829)
                    ·
                      rfl

theorem cell22_246963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_246963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246963 prefixEnd_246963 := by exact prefixLift 246963
  have htrace : WordTrace (prefixWord ++ tailWord_246963) baseStart_246963 baseEnd_246963 := by
    simpa [prefixWord, tailWord_246963, baseEnd_246963] using wordTrace_append hprefix tailTrace_246963
  have hstable : (prefixWord ++ tailWord_246963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246963).length < 2 ^ (prefixWord ++ tailWord_246963).sum := by decide
  have hdescent : baseEnd_246963 < baseStart_246963 := by decide
  rcases family_descends (prefixWord ++ tailWord_246963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246993 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 3, 7]
def baseStart_246993 : Nat := 118140960795 + 246993 * 2 ^ 59
def prefixEnd_246993 : Nat := 4983230072969 + 3 ^ 40 * 246993 * 2
def baseEnd_246993 : Nat := 84550751530704914967737

theorem tailTrace_246993 : CollatzResearch.WordTrace tailWord_246993 prefixEnd_246993 84550751530704914967737 := by
  unfold tailWord_246993
  simp only [CollatzResearch.WordTrace]
  refine ⟨9008574794194018891145633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6005716529462679260763755 9008574794194018891145633)
  ·
    refine ⟨6756431095645514168359225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9008574794194018891145633 6756431095645514168359225)
    ·
      refine ⟨5067323321734135626269419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6756431095645514168359225 5067323321734135626269419)
      ·
        refine ⟨7600984982601203439404129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5067323321734135626269419 7600984982601203439404129)
        ·
          refine ⟨5700738736950902579553097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7600984982601203439404129 5700738736950902579553097)
          ·
            refine ⟨4275554052713176934664823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5700738736950902579553097 4275554052713176934664823)
            ·
              refine ⟨6413331079069765401997235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4275554052713176934664823 6413331079069765401997235)
              ·
                refine ⟨9619996618604648102995853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413331079069765401997235 9619996618604648102995853)
                ·
                  refine ⟨3607498731976743038623445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9619996618604648102995853 3607498731976743038623445)
                  ·
                    refine ⟨84550751530704914967737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3607498731976743038623445 84550751530704914967737)
                    ·
                      rfl

theorem cell22_246993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_246993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_246993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_246993 prefixEnd_246993 := by exact prefixLift 246993
  have htrace : WordTrace (prefixWord ++ tailWord_246993) baseStart_246993 baseEnd_246993 := by
    simpa [prefixWord, tailWord_246993, baseEnd_246993] using wordTrace_append hprefix tailTrace_246993
  have hstable : (prefixWord ++ tailWord_246993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246993).length < 2 ^ (prefixWord ++ tailWord_246993).sum := by decide
  have hdescent : baseEnd_246993 < baseStart_246993 := by decide
  rcases family_descends (prefixWord ++ tailWord_246993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247074 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 6]
def baseStart_247074 : Nat := 118140960795 + 247074 * 2 ^ 59
def prefixEnd_247074 : Nat := 4983230072969 + 3 ^ 40 * 247074 * 2
def baseEnd_247074 : Nat := 28192826495349234564163

theorem tailTrace_247074 : CollatzResearch.WordTrace tailWord_247074 prefixEnd_247074 28192826495349234564163 := by
  unfold tailWord_247074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2252882276725142431211069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6007686071267046483229517 2252882276725142431211069)
  ·
    refine ⟨844830853771928411704151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2252882276725142431211069 844830853771928411704151)
    ·
      refine ⟨1267246280657892617556227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 844830853771928411704151 1267246280657892617556227)
      ·
        refine ⟨1900869420986838926334341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267246280657892617556227 1900869420986838926334341)
        ·
          refine ⟨356413016435032298687689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1900869420986838926334341 356413016435032298687689)
          ·
            refine ⟨267309762326274224015767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356413016435032298687689 267309762326274224015767)
            ·
              refine ⟨400964643489411336023651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267309762326274224015767 400964643489411336023651)
              ·
                refine ⟨601446965234117004035477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400964643489411336023651 601446965234117004035477)
                ·
                  refine ⟨28192826495349234564163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 601446965234117004035477 28192826495349234564163)
                  ·
                    rfl

theorem cell22_247074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_247074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247074 prefixEnd_247074 := by exact prefixLift 247074
  have htrace : WordTrace (prefixWord ++ tailWord_247074) baseStart_247074 baseEnd_247074 := by
    simpa [prefixWord, tailWord_247074, baseEnd_247074] using wordTrace_append hprefix tailTrace_247074
  have hstable : (prefixWord ++ tailWord_247074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247074).length < 2 ^ (prefixWord ++ tailWord_247074).sum := by decide
  have hdescent : baseEnd_247074 < baseStart_247074 := by decide
  rcases family_descends (prefixWord ++ tailWord_247074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247089 : List Nat := [1, 2, 2, 3, 3, 2, 1, 3, 2, 3]
def baseStart_247089 : Nat := 118140960795 + 247089 * 2 ^ 59
def prefixEnd_247089 : Nat := 4983230072969 + 3 ^ 40 * 247089 * 2
def baseEnd_247089 : Nat := 84583614292592664567443

theorem tailTrace_247089 : CollatzResearch.WordTrace tailWord_247089 prefixEnd_247089 84583614292592664567443 := by
  unfold tailWord_247089
  simp only [CollatzResearch.WordTrace]
  refine ⟨9012076201846227286640321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6008050801230818191093547 9012076201846227286640321)
  ·
    refine ⟨6759057151384670464980241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9012076201846227286640321 6759057151384670464980241)
    ·
      refine ⟨5069292863538502848735181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6759057151384670464980241 5069292863538502848735181)
      ·
        refine ⟨1900984823826938568275693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5069292863538502848735181 1900984823826938568275693)
        ·
          refine ⟨712869308935101963103385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1900984823826938568275693 712869308935101963103385)
          ·
            refine ⟨534651981701326472327539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 712869308935101963103385 534651981701326472327539)
            ·
              refine ⟨801977972551989708491309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534651981701326472327539 801977972551989708491309)
              ·
                refine ⟨300741739706996140684241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 801977972551989708491309 300741739706996140684241)
                ·
                  refine ⟨225556304780247105513181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300741739706996140684241 225556304780247105513181)
                  ·
                    refine ⟨84583614292592664567443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225556304780247105513181 84583614292592664567443)
                    ·
                      rfl

theorem cell22_247089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_247089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247089 prefixEnd_247089 := by exact prefixLift 247089
  have htrace : WordTrace (prefixWord ++ tailWord_247089) baseStart_247089 baseEnd_247089 := by
    simpa [prefixWord, tailWord_247089, baseEnd_247089] using wordTrace_append hprefix tailTrace_247089
  have hstable : (prefixWord ++ tailWord_247089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247089).length < 2 ^ (prefixWord ++ tailWord_247089).sum := by decide
  have hdescent : baseEnd_247089 < baseStart_247089 := by decide
  rcases family_descends (prefixWord ++ tailWord_247089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247110 : List Nat := [6, 1, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_247110 : Nat := 118140960795 + 247110 * 2 ^ 59
def prefixEnd_247110 : Nat := 4983230072969 + 3 ^ 40 * 247110 * 2
def baseEnd_247110 : Nat := 84590803021755609792379

theorem tailTrace_247110 : CollatzResearch.WordTrace tailWord_247110 prefixEnd_247110 84590803021755609792379 := by
  unfold tailWord_247110
  simp only [CollatzResearch.WordTrace]
  refine ⟨281651316711567121036087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6008561423180098582103189 281651316711567121036087)
  ·
    refine ⟨422476975067350681554131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281651316711567121036087 422476975067350681554131)
    ·
      refine ⟨633715462601026022331197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422476975067350681554131 633715462601026022331197)
      ·
        refine ⟨237643298475384758374199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 633715462601026022331197 237643298475384758374199)
        ·
          refine ⟨356464947713077137561299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237643298475384758374199 356464947713077137561299)
          ·
            refine ⟨534697421569615706341949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356464947713077137561299 534697421569615706341949)
            ·
              refine ⟨200511533088605889878231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 534697421569615706341949 200511533088605889878231)
              ·
                refine ⟨300767299632908834817347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200511533088605889878231 300767299632908834817347)
                ·
                  refine ⟨451150949449363252226021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300767299632908834817347 451150949449363252226021)
                  ·
                    refine ⟨84590803021755609792379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 451150949449363252226021 84590803021755609792379)
                    ·
                      rfl

theorem cell22_247110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_247110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247110 prefixEnd_247110 := by exact prefixLift 247110
  have htrace : WordTrace (prefixWord ++ tailWord_247110) baseStart_247110 baseEnd_247110 := by
    simpa [prefixWord, tailWord_247110, baseEnd_247110] using wordTrace_append hprefix tailTrace_247110
  have hstable : (prefixWord ++ tailWord_247110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247110).length < 2 ^ (prefixWord ++ tailWord_247110).sum := by decide
  have hdescent : baseEnd_247110 < baseStart_247110 := by decide
  rcases family_descends (prefixWord ++ tailWord_247110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247130 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 7]
def baseStart_247130 : Nat := 118140960795 + 247130 * 2 ^ 59
def prefixEnd_247130 : Nat := 4983230072969 + 3 ^ 40 * 247130 * 2
def baseEnd_247130 : Nat := 28199216476827408097439

theorem tailTrace_247130 : CollatzResearch.WordTrace tailWord_247130 prefixEnd_247130 28199216476827408097439 := by
  unfold tailWord_247130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2253392898674422822220711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6009047729798460859255229 2253392898674422822220711)
  ·
    refine ⟨3380089348011634233331067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2253392898674422822220711 3380089348011634233331067)
    ·
      refine ⟨5070134022017451349996601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3380089348011634233331067 5070134022017451349996601)
      ·
        refine ⟨3802600516513088512497451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5070134022017451349996601 3802600516513088512497451)
        ·
          refine ⟨5703900774769632768746177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3802600516513088512497451 5703900774769632768746177)
          ·
            refine ⟨4277925581077224576559633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5703900774769632768746177 4277925581077224576559633)
            ·
              refine ⟨3208444185807918432419725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4277925581077224576559633 3208444185807918432419725)
              ·
                refine ⟨1203166569677969412157397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3208444185807918432419725 1203166569677969412157397)
                ·
                  refine ⟨28199216476827408097439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1203166569677969412157397 28199216476827408097439)
                  ·
                    rfl

theorem cell22_247130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_247130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247130 prefixEnd_247130 := by exact prefixLift 247130
  have htrace : WordTrace (prefixWord ++ tailWord_247130) baseStart_247130 baseEnd_247130 := by
    simpa [prefixWord, tailWord_247130, baseEnd_247130] using wordTrace_append hprefix tailTrace_247130
  have hstable : (prefixWord ++ tailWord_247130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247130).length < 2 ^ (prefixWord ++ tailWord_247130).sum := by decide
  have hdescent : baseEnd_247130 < baseStart_247130 := by decide
  rcases family_descends (prefixWord ++ tailWord_247130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247198 : List Nat := [4, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_247198 : Nat := 118140960795 + 247198 * 2 ^ 59
def prefixEnd_247198 : Nat := 4983230072969 + 3 ^ 40 * 247198 * 2
def baseEnd_247198 : Nat := 28206975740050904530703

theorem tailTrace_247198 : CollatzResearch.WordTrace tailWord_247198 prefixEnd_247198 28206975740050904530703 := by
  unfold tailWord_247198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127006469806417362794781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6010701172300892601572165 1127006469806417362794781)
  ·
    refine ⟨422627426177406511048043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1127006469806417362794781 422627426177406511048043)
    ·
      refine ⟨633941139266109766572065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422627426177406511048043 633941139266109766572065)
      ·
        refine ⟨475455854449582324929049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633941139266109766572065 475455854449582324929049)
        ·
          refine ⟨356591890837186743696787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475455854449582324929049 356591890837186743696787)
          ·
            refine ⟨534887836255780115545181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356591890837186743696787 534887836255780115545181)
            ·
              refine ⟨200582938595917543329443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 534887836255780115545181 200582938595917543329443)
              ·
                refine ⟨300874407893876314994165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200582938595917543329443 300874407893876314994165)
                ·
                  refine ⟨28206975740050904530703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300874407893876314994165 28206975740050904530703)
                  ·
                    rfl

theorem cell22_247198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_247198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247198 prefixEnd_247198 := by exact prefixLift 247198
  have htrace : WordTrace (prefixWord ++ tailWord_247198) baseStart_247198 baseEnd_247198 := by
    simpa [prefixWord, tailWord_247198, baseEnd_247198] using wordTrace_append hprefix tailTrace_247198
  have hstable : (prefixWord ++ tailWord_247198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247198).length < 2 ^ (prefixWord ++ tailWord_247198).sum := by decide
  have hdescent : baseEnd_247198 < baseStart_247198 := by decide
  rcases family_descends (prefixWord ++ tailWord_247198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247254 : List Nat := [5, 2, 1, 1, 1, 2, 1, 9]
def baseStart_247254 : Nat := 118140960795 + 247254 * 2 ^ 59
def prefixEnd_247254 : Nat := 4983230072969 + 3 ^ 40 * 247254 * 2
def baseEnd_247254 : Nat := 9404455240509692687993

theorem tailTrace_247254 : CollatzResearch.WordTrace tailWord_247254 prefixEnd_247254 9404455240509692687993 := by
  unfold tailWord_247254
  simp only [CollatzResearch.WordTrace]
  refine ⟨563630890390528779149801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6012062830832306977597877 563630890390528779149801)
  ·
    refine ⟨422723167792896584362351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 563630890390528779149801 422723167792896584362351)
    ·
      refine ⟨634084751689344876543527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422723167792896584362351 634084751689344876543527)
      ·
        refine ⟨951127127534017314815291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634084751689344876543527 951127127534017314815291)
        ·
          refine ⟨1426690691301025972222937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951127127534017314815291 1426690691301025972222937)
          ·
            refine ⟨1070018018475769479167203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1426690691301025972222937 1070018018475769479167203)
            ·
              refine ⟨1605027027713654218750805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070018018475769479167203 1605027027713654218750805)
              ·
                refine ⟨9404455240509692687993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1605027027713654218750805 9404455240509692687993)
                ·
                  rfl

theorem cell22_247254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_247254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247254 prefixEnd_247254 := by exact prefixLift 247254
  have htrace : WordTrace (prefixWord ++ tailWord_247254) baseStart_247254 baseEnd_247254 := by
    simpa [prefixWord, tailWord_247254, baseEnd_247254] using wordTrace_append hprefix tailTrace_247254
  have hstable : (prefixWord ++ tailWord_247254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247254).length < 2 ^ (prefixWord ++ tailWord_247254).sum := by decide
  have hdescent : baseEnd_247254 < baseStart_247254 := by decide
  rcases family_descends (prefixWord ++ tailWord_247254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247258 : List Nat := [3, 1, 1, 2, 3, 4, 2, 1, 2, 3]
def baseStart_247258 : Nat := 118140960795 + 247258 * 2 ^ 59
def prefixEnd_247258 : Nat := 4983230072969 + 3 ^ 40 * 247258 * 2
def baseEnd_247258 : Nat := 84641466446332557091925

theorem tailTrace_247258 : CollatzResearch.WordTrace tailWord_247258 prefixEnd_247258 84641466446332557091925 := by
  unfold tailWord_247258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2254560034558492287385607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6012160092155979433028285 2254560034558492287385607)
  ·
    refine ⟨3381840051837738431078411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2254560034558492287385607 3381840051837738431078411)
    ·
      refine ⟨5072760077756607646617617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3381840051837738431078411 5072760077756607646617617)
      ·
        refine ⟨3804570058317455734963213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5072760077756607646617617 3804570058317455734963213)
        ·
          refine ⟨1426713771869045900611205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3804570058317455734963213 1426713771869045900611205)
          ·
            refine ⟨267508832225446106364601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1426713771869045900611205 267508832225446106364601)
            ·
              refine ⟨200631624169084579773451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267508832225446106364601 200631624169084579773451)
              ·
                refine ⟨300947436253626869660177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200631624169084579773451 300947436253626869660177)
                ·
                  refine ⟨225710577190220152245133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300947436253626869660177 225710577190220152245133)
                  ·
                    refine ⟨84641466446332557091925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225710577190220152245133 84641466446332557091925)
                    ·
                      rfl

theorem cell22_247258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_247258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247258 prefixEnd_247258 := by exact prefixLift 247258
  have htrace : WordTrace (prefixWord ++ tailWord_247258) baseStart_247258 baseEnd_247258 := by
    simpa [prefixWord, tailWord_247258, baseEnd_247258] using wordTrace_append hprefix tailTrace_247258
  have hstable : (prefixWord ++ tailWord_247258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247258).length < 2 ^ (prefixWord ++ tailWord_247258).sum := by decide
  have hdescent : baseEnd_247258 < baseStart_247258 := by decide
  rcases family_descends (prefixWord ++ tailWord_247258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247303 : List Nat := [1, 1, 4, 3, 2, 2, 1, 4, 1, 3]
def baseStart_247303 : Nat := 118140960795 + 247303 * 2 ^ 59
def prefixEnd_247303 : Nat := 4983230072969 + 3 ^ 40 * 247303 * 2
def baseEnd_247303 : Nat := 84656870865967439716787

theorem tailTrace_247303 : CollatzResearch.WordTrace tailWord_247303 prefixEnd_247303 84656870865967439716787 := by
  unfold tailWord_247303
  simp only [CollatzResearch.WordTrace]
  refine ⟨9019881423070941834930563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6013254282047294556620375 9019881423070941834930563)
  ·
    refine ⟨13529822134606412752395845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9019881423070941834930563 13529822134606412752395845)
    ·
      refine ⟨2536841650238702391074221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13529822134606412752395845 2536841650238702391074221)
      ·
        refine ⟨951315618839513396652833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2536841650238702391074221 951315618839513396652833)
        ·
          refine ⟨713486714129635047489625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951315618839513396652833 713486714129635047489625)
          ·
            refine ⟨535115035597226285617219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713486714129635047489625 535115035597226285617219)
            ·
              refine ⟨802672553395839428425829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535115035597226285617219 802672553395839428425829)
              ·
                refine ⟨150501103761719892829843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 802672553395839428425829 150501103761719892829843)
                ·
                  refine ⟨225751655642579839244765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150501103761719892829843 225751655642579839244765)
                  ·
                    refine ⟨84656870865967439716787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225751655642579839244765 84656870865967439716787)
                    ·
                      rfl

theorem cell22_247303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_247303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247303 prefixEnd_247303 := by exact prefixLift 247303
  have htrace : WordTrace (prefixWord ++ tailWord_247303) baseStart_247303 baseEnd_247303 := by
    simpa [prefixWord, tailWord_247303, baseEnd_247303] using wordTrace_append hprefix tailTrace_247303
  have hstable : (prefixWord ++ tailWord_247303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247303).length < 2 ^ (prefixWord ++ tailWord_247303).sum := by decide
  have hdescent : baseEnd_247303 < baseStart_247303 := by decide
  rcases family_descends (prefixWord ++ tailWord_247303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247327 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 8]
def baseStart_247327 : Nat := 118140960795 + 247327 * 2 ^ 59
def prefixEnd_247327 : Nat := 4983230072969 + 3 ^ 40 * 247327 * 2
def baseEnd_247327 : Nat := 28221695518813125705571

theorem tailTrace_247327 : CollatzResearch.WordTrace tailWord_247327 prefixEnd_247327 28221695518813125705571 := by
  unfold tailWord_247327
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020756774983993933804235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6013837849989329289202823 9020756774983993933804235)
  ·
    refine ⟨13531135162475990900706353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9020756774983993933804235 13531135162475990900706353)
    ·
      refine ⟨10148351371856993175529765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13531135162475990900706353 10148351371856993175529765)
      ·
        refine ⟨1902815882223186220411831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10148351371856993175529765 1902815882223186220411831)
        ·
          refine ⟨2854223823334779330617747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902815882223186220411831 2854223823334779330617747)
          ·
            refine ⟨4281335735002168995926621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854223823334779330617747 4281335735002168995926621)
            ·
              refine ⟨1605500900625813373472483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4281335735002168995926621 1605500900625813373472483)
              ·
                refine ⟨2408251350938720060208725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605500900625813373472483 2408251350938720060208725)
                ·
                  refine ⟨28221695518813125705571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2408251350938720060208725 28221695518813125705571)
                  ·
                    rfl

theorem cell22_247327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 8].length) (baseStart_247327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247327 prefixEnd_247327 := by exact prefixLift 247327
  have htrace : WordTrace (prefixWord ++ tailWord_247327) baseStart_247327 baseEnd_247327 := by
    simpa [prefixWord, tailWord_247327, baseEnd_247327] using wordTrace_append hprefix tailTrace_247327
  have hstable : (prefixWord ++ tailWord_247327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247327).length < 2 ^ (prefixWord ++ tailWord_247327).sum := by decide
  have hdescent : baseEnd_247327 < baseStart_247327 := by decide
  rcases family_descends (prefixWord ++ tailWord_247327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247329 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 3, 4]
def baseStart_247329 : Nat := 118140960795 + 247329 * 2 ^ 59
def prefixEnd_247329 : Nat := 4983230072969 + 3 ^ 40 * 247329 * 2
def baseEnd_247329 : Nat := 84665771197312038566707

theorem tailTrace_247329 : CollatzResearch.WordTrace tailWord_247329 prefixEnd_247329 84665771197312038566707 := by
  unfold tailWord_247329
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020829720976748275377041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6013886480651165516918027 9020829720976748275377041)
  ·
    refine ⟨6765622290732561206532781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9020829720976748275377041 6765622290732561206532781)
    ·
      refine ⟨2537108359024710452449793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6765622290732561206532781 2537108359024710452449793)
      ·
        refine ⟨1902831269268532839337345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2537108359024710452449793 1902831269268532839337345)
        ·
          refine ⟨1427123451951399629503009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1902831269268532839337345 1427123451951399629503009)
          ·
            refine ⟨1070342588963549722127257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1427123451951399629503009 1070342588963549722127257)
            ·
              refine ⟨802756941722662291595443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070342588963549722127257 802756941722662291595443)
              ·
                refine ⟨1204135412583993437393165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802756941722662291595443 1204135412583993437393165)
                ·
                  refine ⟨451550779718997539022437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204135412583993437393165 451550779718997539022437)
                  ·
                    refine ⟨84665771197312038566707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 451550779718997539022437 84665771197312038566707)
                    ·
                      rfl

theorem cell22_247329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_247329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247329 prefixEnd_247329 := by exact prefixLift 247329
  have htrace : WordTrace (prefixWord ++ tailWord_247329) baseStart_247329 baseEnd_247329 := by
    simpa [prefixWord, tailWord_247329, baseEnd_247329] using wordTrace_append hprefix tailTrace_247329
  have hstable : (prefixWord ++ tailWord_247329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247329).length < 2 ^ (prefixWord ++ tailWord_247329).sum := by decide
  have hdescent : baseEnd_247329 < baseStart_247329 := by decide
  rcases family_descends (prefixWord ++ tailWord_247329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247350 : List Nat := [5, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_247350 : Nat := 118140960795 + 247350 * 2 ^ 59
def prefixEnd_247350 : Nat := 4983230072969 + 3 ^ 40 * 247350 * 2
def baseEnd_247350 : Nat := 28224319975491661263881

theorem tailTrace_247350 : CollatzResearch.WordTrace tailWord_247350 prefixEnd_247350 28224319975491661263881 := by
  unfold tailWord_247350
  simp only [CollatzResearch.WordTrace]
  refine ⟨563849728368791803868219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6014397102600445907927669 563849728368791803868219)
  ·
    refine ⟨845774592553187705802329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 563849728368791803868219 845774592553187705802329)
    ·
      refine ⟨634330944414890779351747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 845774592553187705802329 634330944414890779351747)
      ·
        refine ⟨951496416622336169027621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634330944414890779351747 951496416622336169027621)
        ·
          refine ⟨178405578116688031692679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 951496416622336169027621 178405578116688031692679)
          ·
            refine ⟨267608367175032047539019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178405578116688031692679 267608367175032047539019)
            ·
              refine ⟨401412550762548071308529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267608367175032047539019 401412550762548071308529)
              ·
                refine ⟨301059413071911053481397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401412550762548071308529 301059413071911053481397)
                ·
                  refine ⟨28224319975491661263881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301059413071911053481397 28224319975491661263881)
                  ·
                    rfl

theorem cell22_247350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_247350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247350 prefixEnd_247350 := by exact prefixLift 247350
  have htrace : WordTrace (prefixWord ++ tailWord_247350) baseStart_247350 baseEnd_247350 := by
    simpa [prefixWord, tailWord_247350, baseEnd_247350] using wordTrace_append hprefix tailTrace_247350
  have hstable : (prefixWord ++ tailWord_247350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247350).length < 2 ^ (prefixWord ++ tailWord_247350).sum := by decide
  have hdescent : baseEnd_247350 < baseStart_247350 := by decide
  rcases family_descends (prefixWord ++ tailWord_247350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247361 : List Nat := [1, 2, 5, 1, 1, 1, 1, 6, 4]
def baseStart_247361 : Nat := 118140960795 + 247361 * 2 ^ 59
def prefixEnd_247361 : Nat := 4983230072969 + 3 ^ 40 * 247361 * 2
def baseEnd_247361 : Nat := 28225575150424873922203

theorem tailTrace_247361 : CollatzResearch.WordTrace tailWord_247361 prefixEnd_247361 28225575150424873922203 := by
  unfold tailWord_247361
  simp only [CollatzResearch.WordTrace]
  refine ⟨9021996856860817740541937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6014664571240545160361291 9021996856860817740541937)
  ·
    refine ⟨6766497642645613305406453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9021996856860817740541937 6766497642645613305406453)
    ·
      refine ⟨634359153998026247381855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6766497642645613305406453 634359153998026247381855)
      ·
        refine ⟨951538730997039371072783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634359153998026247381855 951538730997039371072783)
        ·
          refine ⟨1427308096495559056609175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951538730997039371072783 1427308096495559056609175)
          ·
            refine ⟨2140962144743338584913763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427308096495559056609175 2140962144743338584913763)
            ·
              refine ⟨3211443217115007877370645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140962144743338584913763 3211443217115007877370645)
              ·
                refine ⟨150536400802265994251749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3211443217115007877370645 150536400802265994251749)
                ·
                  refine ⟨28225575150424873922203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150536400802265994251749 28225575150424873922203)
                  ·
                    rfl

theorem cell22_247361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 4].length) (baseStart_247361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247361 prefixEnd_247361 := by exact prefixLift 247361
  have htrace : WordTrace (prefixWord ++ tailWord_247361) baseStart_247361 baseEnd_247361 := by
    simpa [prefixWord, tailWord_247361, baseEnd_247361] using wordTrace_append hprefix tailTrace_247361
  have hstable : (prefixWord ++ tailWord_247361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247361).length < 2 ^ (prefixWord ++ tailWord_247361).sum := by decide
  have hdescent : baseEnd_247361 < baseStart_247361 := by decide
  rcases family_descends (prefixWord ++ tailWord_247361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247406 : List Nat := [4, 1, 2, 2, 3, 2, 8]
def baseStart_247406 : Nat := 118140960795 + 247406 * 2 ^ 59
def prefixEnd_247406 : Nat := 4983230072969 + 3 ^ 40 * 247406 * 2
def baseEnd_247406 : Nat := 3136745550774426088573

theorem tailTrace_247406 : CollatzResearch.WordTrace tailWord_247406 prefixEnd_247406 3136745550774426088573 := by
  unfold tailWord_247406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127954767712223803241259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6015758761131860283953381 1127954767712223803241259)
  ·
    refine ⟨1691932151568335704861889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1127954767712223803241259 1691932151568335704861889)
    ·
      refine ⟨1268949113676251778646417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1691932151568335704861889 1268949113676251778646417)
      ·
        refine ⟨951711835257188833984813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1268949113676251778646417 951711835257188833984813)
        ·
          refine ⟨356891938221445812744305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 951711835257188833984813 356891938221445812744305)
          ·
            refine ⟨267668953666084359558229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356891938221445812744305 267668953666084359558229)
            ·
              refine ⟨3136745550774426088573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 267668953666084359558229 3136745550774426088573)
              ·
                rfl

theorem cell22_247406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 8].length) (baseStart_247406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247406 prefixEnd_247406 := by exact prefixLift 247406
  have htrace : WordTrace (prefixWord ++ tailWord_247406) baseStart_247406 baseEnd_247406 := by
    simpa [prefixWord, tailWord_247406, baseEnd_247406] using wordTrace_append hprefix tailTrace_247406
  have hstable : (prefixWord ++ tailWord_247406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247406).length < 2 ^ (prefixWord ++ tailWord_247406).sum := by decide
  have hdescent : baseEnd_247406 < baseStart_247406 := by decide
  rcases family_descends (prefixWord ++ tailWord_247406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247511 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 4, 3]
def baseStart_247511 : Nat := 118140960795 + 247511 * 2 ^ 59
def prefixEnd_247511 : Nat := 4983230072969 + 3 ^ 40 * 247511 * 2
def baseEnd_247511 : Nat := 84728073516724230516149

theorem tailTrace_247511 : CollatzResearch.WordTrace tailWord_247511 prefixEnd_247511 84728073516724230516149 := by
  unfold tailWord_247511
  simp only [CollatzResearch.WordTrace]
  refine ⟨9027467806317393358502387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6018311870878262239001591 9027467806317393358502387)
  ·
    refine ⟨13541201709476090037753581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9027467806317393358502387 13541201709476090037753581)
    ·
      refine ⟨5077950641053533764157593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13541201709476090037753581 5077950641053533764157593)
      ·
        refine ⟨3808462980790150323118195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5077950641053533764157593 3808462980790150323118195)
        ·
          refine ⟨5712694471185225484677293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808462980790150323118195 5712694471185225484677293)
          ·
            refine ⟨2142260426694459556753985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5712694471185225484677293 2142260426694459556753985)
            ·
              refine ⟨1606695320020844667565489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2142260426694459556753985 1606695320020844667565489)
              ·
                refine ⟨1205021490015633500674117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1606695320020844667565489 1205021490015633500674117)
                ·
                  refine ⟨225941529377931281376397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1205021490015633500674117 225941529377931281376397)
                  ·
                    refine ⟨84728073516724230516149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225941529377931281376397 84728073516724230516149)
                    ·
                      rfl

theorem cell22_247511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_247511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247511 prefixEnd_247511 := by exact prefixLift 247511
  have htrace : WordTrace (prefixWord ++ tailWord_247511) baseStart_247511 baseEnd_247511 := by
    simpa [prefixWord, tailWord_247511, baseEnd_247511] using wordTrace_append hprefix tailTrace_247511
  have hstable : (prefixWord ++ tailWord_247511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247511).length < 2 ^ (prefixWord ++ tailWord_247511).sum := by decide
  have hdescent : baseEnd_247511 < baseStart_247511 := by decide
  rcases family_descends (prefixWord ++ tailWord_247511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247513 : List Nat := [1, 2, 1, 2, 3, 4, 2, 3, 4]
def baseStart_247513 : Nat := 118140960795 + 247513 * 2 ^ 59
def prefixEnd_247513 : Nat := 4983230072969 + 3 ^ 40 * 247513 * 2
def baseEnd_247513 : Nat := 28242919385865630655381

theorem tailTrace_247513 : CollatzResearch.WordTrace tailWord_247513 prefixEnd_247513 28242919385865630655381 := by
  unfold tailWord_247513
  simp only [CollatzResearch.WordTrace]
  refine ⟨9027540752310147700075193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6018360501540098466716795 9027540752310147700075193)
  ·
    refine ⟨6770655564232610775056395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9027540752310147700075193 6770655564232610775056395)
    ·
      refine ⟨10155983346348916162584593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6770655564232610775056395 10155983346348916162584593)
      ·
        refine ⟨7616987509761687121938445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10155983346348916162584593 7616987509761687121938445)
        ·
          refine ⟨2856370316160632670726917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7616987509761687121938445 2856370316160632670726917)
          ·
            refine ⟨535569434280118625761297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2856370316160632670726917 535569434280118625761297)
            ·
              refine ⟨401677075710088969320973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535569434280118625761297 401677075710088969320973)
              ·
                refine ⟨150628903391283363495365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401677075710088969320973 150628903391283363495365)
                ·
                  refine ⟨28242919385865630655381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150628903391283363495365 28242919385865630655381)
                  ·
                    rfl

theorem cell22_247513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 4].length) (baseStart_247513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247513 prefixEnd_247513 := by exact prefixLift 247513
  have htrace : WordTrace (prefixWord ++ tailWord_247513) baseStart_247513 baseEnd_247513 := by
    simpa [prefixWord, tailWord_247513, baseEnd_247513] using wordTrace_append hprefix tailTrace_247513
  have hstable : (prefixWord ++ tailWord_247513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247513).length < 2 ^ (prefixWord ++ tailWord_247513).sum := by decide
  have hdescent : baseEnd_247513 < baseStart_247513 := by decide
  rcases family_descends (prefixWord ++ tailWord_247513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247524 : List Nat := [2, 3, 1, 1, 1, 3, 11]
def baseStart_247524 : Nat := 118140960795 + 247524 * 2 ^ 59
def prefixEnd_247524 : Nat := 4983230072969 + 3 ^ 40 * 247524 * 2
def baseEnd_247524 : Nat := 3138241617866538145967

theorem tailTrace_247524 : CollatzResearch.WordTrace tailWord_247524 prefixEnd_247524 3138241617866538145967 := by
  unfold tailWord_247524
  simp only [CollatzResearch.WordTrace]
  refine ⟨4513970977635148289362813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6018627970180197719150417 4513970977635148289362813)
  ·
    refine ⟨1692739116613180608511055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4513970977635148289362813 1692739116613180608511055)
    ·
      refine ⟨2539108674919770912766583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1692739116613180608511055 2539108674919770912766583)
      ·
        refine ⟨3808663012379656369149875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2539108674919770912766583 3808663012379656369149875)
        ·
          refine ⟨5712994518569484553724813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808663012379656369149875 5712994518569484553724813)
          ·
            refine ⟨2142372944463556707646805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5712994518569484553724813 2142372944463556707646805)
            ·
              refine ⟨3138241617866538145967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2142372944463556707646805 3138241617866538145967)
              ·
                rfl

theorem cell22_247524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 11].length) (baseStart_247524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247524 prefixEnd_247524 := by exact prefixLift 247524
  have htrace : WordTrace (prefixWord ++ tailWord_247524) baseStart_247524 baseEnd_247524 := by
    simpa [prefixWord, tailWord_247524, baseEnd_247524] using wordTrace_append hprefix tailTrace_247524
  have hstable : (prefixWord ++ tailWord_247524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247524).length < 2 ^ (prefixWord ++ tailWord_247524).sum := by decide
  have hdescent : baseEnd_247524 < baseStart_247524 := by decide
  rcases family_descends (prefixWord ++ tailWord_247524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247528 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 4, 3]
def baseStart_247528 : Nat := 118140960795 + 247528 * 2 ^ 59
def prefixEnd_247528 : Nat := 4983230072969 + 3 ^ 40 * 247528 * 2
def baseEnd_247528 : Nat := 84733892964141852841097

theorem tailTrace_247528 : CollatzResearch.WordTrace tailWord_247528 prefixEnd_247528 84733892964141852841097 := by
  unfold tailWord_247528
  simp only [CollatzResearch.WordTrace]
  refine ⟨4514043923627902630935619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6018725231503870174580825 4514043923627902630935619)
  ·
    refine ⟨6771065885441853946403429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4514043923627902630935619 6771065885441853946403429)
    ·
      refine ⟨1269574853520347614950643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6771065885441853946403429 1269574853520347614950643)
      ·
        refine ⟨1904362280280521422425965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269574853520347614950643 1904362280280521422425965)
        ·
          refine ⟨714135855105195533409737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1904362280280521422425965 714135855105195533409737)
          ·
            refine ⟨535601891328896650057303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714135855105195533409737 535601891328896650057303)
            ·
              refine ⟨803402836993344975085955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535601891328896650057303 803402836993344975085955)
              ·
                refine ⟨1205104255490017462628933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803402836993344975085955 1205104255490017462628933)
                ·
                  refine ⟨225957047904378274242925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1205104255490017462628933 225957047904378274242925)
                  ·
                    refine ⟨84733892964141852841097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225957047904378274242925 84733892964141852841097)
                    ·
                      rfl

theorem cell22_247528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_247528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247528 prefixEnd_247528 := by exact prefixLift 247528
  have htrace : WordTrace (prefixWord ++ tailWord_247528) baseStart_247528 baseEnd_247528 := by
    simpa [prefixWord, tailWord_247528, baseEnd_247528] using wordTrace_append hprefix tailTrace_247528
  have hstable : (prefixWord ++ tailWord_247528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247528).length < 2 ^ (prefixWord ++ tailWord_247528).sum := by decide
  have hdescent : baseEnd_247528 < baseStart_247528 := by decide
  rcases family_descends (prefixWord ++ tailWord_247528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247586 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 7]
def baseStart_247586 : Nat := 118140960795 + 247586 * 2 ^ 59
def prefixEnd_247586 : Nat := 4983230072969 + 3 ^ 40 * 247586 * 2
def baseEnd_247586 : Nat := 28251249183149678296973

theorem tailTrace_247586 : CollatzResearch.WordTrace tailWord_247586 prefixEnd_247586 28251249183149678296973 := by
  unfold tailWord_247586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2257550820261420291870653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6020135520697120778321741 2257550820261420291870653)
  ·
    refine ⟨846581557598032609451495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2257550820261420291870653 846581557598032609451495)
    ·
      refine ⟨1269872336397048914177243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 846581557598032609451495 1269872336397048914177243)
      ·
        refine ⟨1904808504595573371265865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269872336397048914177243 1904808504595573371265865)
        ·
          refine ⟨1428606378446680028449399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1904808504595573371265865 1428606378446680028449399)
          ·
            refine ⟨2142909567670020042674099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428606378446680028449399 2142909567670020042674099)
            ·
              refine ⟨3214364351505030064011149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142909567670020042674099 3214364351505030064011149)
              ·
                refine ⟨1205386631814386274004181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3214364351505030064011149 1205386631814386274004181)
                ·
                  refine ⟨28251249183149678296973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1205386631814386274004181 28251249183149678296973)
                  ·
                    rfl

theorem cell22_247586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_247586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247586 prefixEnd_247586 := by exact prefixLift 247586
  have htrace : WordTrace (prefixWord ++ tailWord_247586) baseStart_247586 baseEnd_247586 := by
    simpa [prefixWord, tailWord_247586, baseEnd_247586] using wordTrace_append hprefix tailTrace_247586
  have hstable : (prefixWord ++ tailWord_247586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247586).length < 2 ^ (prefixWord ++ tailWord_247586).sum := by decide
  have hdescent : baseEnd_247586 < baseStart_247586 := by decide
  rcases family_descends (prefixWord ++ tailWord_247586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247603 : List Nat := [1, 1, 1, 2, 7, 1, 1, 3, 5]
def baseStart_247603 : Nat := 118140960795 + 247603 * 2 ^ 59
def prefixEnd_247603 : Nat := 4983230072969 + 3 ^ 40 * 247603 * 2
def baseEnd_247603 : Nat := 28253188998955552405289

theorem tailTrace_247603 : CollatzResearch.WordTrace tailWord_247603 prefixEnd_247603 28253188998955552405289 := by
  unfold tailWord_247603
  simp only [CollatzResearch.WordTrace]
  refine ⟨9030823321984093070851463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6020548881322728713900975 9030823321984093070851463)
  ·
    refine ⟨13546234982976139606277195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9030823321984093070851463 13546234982976139606277195)
    ·
      refine ⟨20319352474464209409415793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13546234982976139606277195 20319352474464209409415793)
      ·
        refine ⟨15239514355848157057061845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20319352474464209409415793 15239514355848157057061845)
        ·
          refine ⟨357176117715191181024887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15239514355848157057061845 357176117715191181024887)
          ·
            refine ⟨535764176572786771537331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357176117715191181024887 535764176572786771537331)
            ·
              refine ⟨803646264859180157305997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535764176572786771537331 803646264859180157305997)
              ·
                refine ⟨301367349322192558989749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 803646264859180157305997 301367349322192558989749)
                ·
                  refine ⟨28253188998955552405289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301367349322192558989749 28253188998955552405289)
                  ·
                    rfl

theorem cell22_247603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 5].length) (baseStart_247603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247603 prefixEnd_247603 := by exact prefixLift 247603
  have htrace : WordTrace (prefixWord ++ tailWord_247603) baseStart_247603 baseEnd_247603 := by
    simpa [prefixWord, tailWord_247603, baseEnd_247603] using wordTrace_append hprefix tailTrace_247603
  have hstable : (prefixWord ++ tailWord_247603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247603).length < 2 ^ (prefixWord ++ tailWord_247603).sum := by decide
  have hdescent : baseEnd_247603 < baseStart_247603 := by decide
  rcases family_descends (prefixWord ++ tailWord_247603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247714 : List Nat := [3, 3, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_247714 : Nat := 118140960795 + 247714 * 2 ^ 59
def prefixEnd_247714 : Nat := 4983230072969 + 3 ^ 40 * 247714 * 2
def baseEnd_247714 : Nat := 84797564565299367690527

theorem tailTrace_247714 : CollatzResearch.WordTrace tailWord_247714 prefixEnd_247714 84797564565299367690527 := by
  unfold tailWord_247714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2258717956145489757035549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6023247883054639352094797 2258717956145489757035549)
  ·
    refine ⟨847019233554558658888331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2258717956145489757035549 847019233554558658888331)
    ·
      refine ⟨1270528850331837988332497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 847019233554558658888331 1270528850331837988332497)
      ·
        refine ⟨952896637748878491249373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1270528850331837988332497 952896637748878491249373)
        ·
          refine ⟨357336239155829434218515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 952896637748878491249373 357336239155829434218515)
          ·
            refine ⟨536004358733744151327773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357336239155829434218515 536004358733744151327773)
            ·
              refine ⟨201001634525154056747915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 536004358733744151327773 201001634525154056747915)
              ·
                refine ⟨301502451787731085121873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201001634525154056747915 301502451787731085121873)
                ·
                  refine ⟨226126838840798313841405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301502451787731085121873 226126838840798313841405)
                  ·
                    refine ⟨84797564565299367690527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 226126838840798313841405 84797564565299367690527)
                    ·
                      rfl

theorem cell22_247714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_247714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247714 prefixEnd_247714 := by exact prefixLift 247714
  have htrace : WordTrace (prefixWord ++ tailWord_247714) baseStart_247714 baseEnd_247714 := by
    simpa [prefixWord, tailWord_247714, baseEnd_247714] using wordTrace_append hprefix tailTrace_247714
  have hstable : (prefixWord ++ tailWord_247714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247714).length < 2 ^ (prefixWord ++ tailWord_247714).sum := by decide
  have hdescent : baseEnd_247714 < baseStart_247714 := by decide
  rcases family_descends (prefixWord ++ tailWord_247714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247768 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 3, 4]
def baseStart_247768 : Nat := 118140960795 + 247768 * 2 ^ 59
def prefixEnd_247768 : Nat := 4983230072969 + 3 ^ 40 * 247768 * 2
def baseEnd_247768 : Nat := 84816049868861226840361

theorem tailTrace_247768 : CollatzResearch.WordTrace tailWord_247768 prefixEnd_247768 84816049868861226840361 := by
  unfold tailWord_247768
  simp only [CollatzResearch.WordTrace]
  refine ⟨4518420683193163125303979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6024560910924217500405305 4518420683193163125303979)
  ·
    refine ⟨6777631024789744687955969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4518420683193163125303979 6777631024789744687955969)
    ·
      refine ⟨5083223268592308515966977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6777631024789744687955969 5083223268592308515966977)
      ·
        refine ⟨3812417451444231386975233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5083223268592308515966977 3812417451444231386975233)
        ·
          refine ⟨2859313088583173540231425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3812417451444231386975233 2859313088583173540231425)
          ·
            refine ⟨2144484816437380155173569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2859313088583173540231425 2144484816437380155173569)
            ·
              refine ⟨1608363612328035116380177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2144484816437380155173569 1608363612328035116380177)
              ·
                refine ⟨1206272709246026337285133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1608363612328035116380177 1206272709246026337285133)
                ·
                  refine ⟨452352265967259876481925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206272709246026337285133 452352265967259876481925)
                  ·
                    refine ⟨84816049868861226840361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 452352265967259876481925 84816049868861226840361)
                    ·
                      rfl

theorem cell22_247768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_247768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247768 prefixEnd_247768 := by exact prefixLift 247768
  have htrace : WordTrace (prefixWord ++ tailWord_247768) baseStart_247768 baseEnd_247768 := by
    simpa [prefixWord, tailWord_247768, baseEnd_247768] using wordTrace_append hprefix tailTrace_247768
  have hstable : (prefixWord ++ tailWord_247768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247768).length < 2 ^ (prefixWord ++ tailWord_247768).sum := by decide
  have hdescent : baseEnd_247768 < baseStart_247768 := by decide
  rcases family_descends (prefixWord ++ tailWord_247768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247845 : List Nat := [1, 3, 1, 2, 2, 4, 3, 6]
def baseStart_247845 : Nat := 118140960795 + 247845 * 2 ^ 59
def prefixEnd_247845 : Nat := 4983230072969 + 3 ^ 40 * 247845 * 2
def baseEnd_247845 : Nat := 9426934282495410296125

theorem tailTrace_247845 : CollatzResearch.WordTrace tailWord_247845 prefixEnd_247845 9426934282495410296125 := by
  unfold tailWord_247845
  simp only [CollatzResearch.WordTrace]
  refine ⟨9039649787107368401160989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6026433191404912267440659 9039649787107368401160989)
  ·
    refine ⟨3389868670165263150435371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9039649787107368401160989 3389868670165263150435371)
    ·
      refine ⟨5084803005247894725653057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3389868670165263150435371 5084803005247894725653057)
      ·
        refine ⟨3813602253935921044239793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5084803005247894725653057 3813602253935921044239793)
        ·
          refine ⟨2860201690451940783179845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3813602253935921044239793 2860201690451940783179845)
          ·
            refine ⟨536287816959738896846221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2860201690451940783179845 536287816959738896846221)
            ·
              refine ⟨201107931359902086317333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 536287816959738896846221 201107931359902086317333)
              ·
                refine ⟨9426934282495410296125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201107931359902086317333 9426934282495410296125)
                ·
                  rfl

theorem cell22_247845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 6].length) (baseStart_247845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247845 prefixEnd_247845 := by exact prefixLift 247845
  have htrace : WordTrace (prefixWord ++ tailWord_247845) baseStart_247845 baseEnd_247845 := by
    simpa [prefixWord, tailWord_247845, baseEnd_247845] using wordTrace_append hprefix tailTrace_247845
  have hstable : (prefixWord ++ tailWord_247845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247845).length < 2 ^ (prefixWord ++ tailWord_247845).sum := by decide
  have hdescent : baseEnd_247845 < baseStart_247845 := by decide
  rcases family_descends (prefixWord ++ tailWord_247845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247847 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 1, 6]
def baseStart_247847 : Nat := 118140960795 + 247847 * 2 ^ 59
def prefixEnd_247847 : Nat := 4983230072969 + 3 ^ 40 * 247847 * 2
def baseEnd_247847 : Nat := 84843093183331354115119

theorem tailTrace_247847 : CollatzResearch.WordTrace tailWord_247847 prefixEnd_247847 84843093183331354115119 := by
  unfold tailWord_247847
  simp only [CollatzResearch.WordTrace]
  refine ⟨9039722733100122742733795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6026481822066748495155863 9039722733100122742733795)
  ·
    refine ⟨13559584099650184114100693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9039722733100122742733795 13559584099650184114100693)
    ·
      refine ⟨317802752335551190174235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13559584099650184114100693 317802752335551190174235)
      ·
        refine ⟨476704128503326785261353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317802752335551190174235 476704128503326785261353)
        ·
          refine ⟨357528096377495088946015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476704128503326785261353 357528096377495088946015)
          ·
            refine ⟨536292144566242633419023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357528096377495088946015 536292144566242633419023)
            ·
              refine ⟨804438216849363950128535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536292144566242633419023 804438216849363950128535)
              ·
                refine ⟨1206657325274045925192803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804438216849363950128535 1206657325274045925192803)
                ·
                  refine ⟨1809985987911068887789205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1206657325274045925192803 1809985987911068887789205)
                  ·
                    refine ⟨84843093183331354115119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1809985987911068887789205 84843093183331354115119)
                    ·
                      rfl

theorem cell22_247847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_247847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247847 prefixEnd_247847 := by exact prefixLift 247847
  have htrace : WordTrace (prefixWord ++ tailWord_247847) baseStart_247847 baseEnd_247847 := by
    simpa [prefixWord, tailWord_247847, baseEnd_247847] using wordTrace_append hprefix tailTrace_247847
  have hstable : (prefixWord ++ tailWord_247847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247847).length < 2 ^ (prefixWord ++ tailWord_247847).sum := by decide
  have hdescent : baseEnd_247847 < baseStart_247847 := by decide
  rcases family_descends (prefixWord ++ tailWord_247847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247963 : List Nat := [1, 1, 1, 1, 1, 1, 2, 14]
def baseStart_247963 : Nat := 118140960795 + 247963 * 2 ^ 59
def prefixEnd_247963 : Nat := 4983230072969 + 3 ^ 40 * 247963 * 2
def baseEnd_247963 : Nat := 9431422483771746468307

theorem tailTrace_247963 : CollatzResearch.WordTrace tailWord_247963 prefixEnd_247963 9431422483771746468307 := by
  unfold tailWord_247963
  simp only [CollatzResearch.WordTrace]
  refine ⟨9043953600679874553956543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6029302400453249702637695 9043953600679874553956543)
  ·
    refine ⟨13565930401019811830934815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9043953600679874553956543 13565930401019811830934815)
    ·
      refine ⟨20348895601529717746402223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13565930401019811830934815 20348895601529717746402223)
      ·
        refine ⟨30523343402294576619603335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20348895601529717746402223 30523343402294576619603335)
        ·
          refine ⟨45785015103441864929405003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30523343402294576619603335 45785015103441864929405003)
          ·
            refine ⟨68677522655162797394107505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45785015103441864929405003 68677522655162797394107505)
            ·
              refine ⟨51508141991372098045580629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68677522655162797394107505 51508141991372098045580629)
              ·
                refine ⟨9431422483771746468307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 51508141991372098045580629 9431422483771746468307)
                ·
                  rfl

theorem cell22_247963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 14].length) (baseStart_247963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247963 prefixEnd_247963 := by exact prefixLift 247963
  have htrace : WordTrace (prefixWord ++ tailWord_247963) baseStart_247963 baseEnd_247963 := by
    simpa [prefixWord, tailWord_247963, baseEnd_247963] using wordTrace_append hprefix tailTrace_247963
  have hstable : (prefixWord ++ tailWord_247963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247963).length < 2 ^ (prefixWord ++ tailWord_247963).sum := by decide
  have hdescent : baseEnd_247963 < baseStart_247963 := by decide
  rcases family_descends (prefixWord ++ tailWord_247963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247967 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 1, 5]
def baseStart_247967 : Nat := 118140960795 + 247967 * 2 ^ 59
def prefixEnd_247967 : Nat := 4983230072969 + 3 ^ 40 * 247967 * 2
def baseEnd_247967 : Nat := 84884171635691041114751

theorem tailTrace_247967 : CollatzResearch.WordTrace tailWord_247967 prefixEnd_247967 84884171635691041114751 := by
  unfold tailWord_247967
  simp only [CollatzResearch.WordTrace]
  refine ⟨9044099492665383237102155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6029399661776922158068103 9044099492665383237102155)
  ·
    refine ⟨13566149238998074855653233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9044099492665383237102155 13566149238998074855653233)
    ·
      refine ⟨10174611929248556141739925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13566149238998074855653233 10174611929248556141739925)
      ·
        refine ⟨476934934183526069144059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10174611929248556141739925 476934934183526069144059)
        ·
          refine ⟨715402401275289103716089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476934934183526069144059 715402401275289103716089)
          ·
            refine ⟨536551800956466827787067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715402401275289103716089 536551800956466827787067)
            ·
              refine ⟨804827701434700241680601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536551800956466827787067 804827701434700241680601)
              ·
                refine ⟨603620776076025181260451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804827701434700241680601 603620776076025181260451)
                ·
                  refine ⟨905431164114037771890677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603620776076025181260451 905431164114037771890677)
                  ·
                    refine ⟨84884171635691041114751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 905431164114037771890677 84884171635691041114751)
                    ·
                      rfl

theorem cell22_247967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_247967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_247967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_247967 prefixEnd_247967 := by exact prefixLift 247967
  have htrace : WordTrace (prefixWord ++ tailWord_247967) baseStart_247967 baseEnd_247967 := by
    simpa [prefixWord, tailWord_247967, baseEnd_247967] using wordTrace_append hprefix tailTrace_247967
  have hstable : (prefixWord ++ tailWord_247967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247967).length < 2 ^ (prefixWord ++ tailWord_247967).sum := by decide
  have hdescent : baseEnd_247967 < baseStart_247967 := by decide
  rcases family_descends (prefixWord ++ tailWord_247967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248010 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_248010 : Nat := 118140960795 + 248010 * 2 ^ 59
def prefixEnd_248010 : Nat := 4983230072969 + 3 ^ 40 * 248010 * 2
def baseEnd_248010 : Nat := 84898891414453262289619

theorem tailTrace_248010 : CollatzResearch.WordTrace tailWord_248010 prefixEnd_248010 84898891414453262289619 := by
  unfold tailWord_248010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261416957877400395229371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6030445221006401053944989 2261416957877400395229371)
  ·
    refine ⟨3392125436816100592844057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2261416957877400395229371 3392125436816100592844057)
    ·
      refine ⟨2544094077612075444633043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3392125436816100592844057 2544094077612075444633043)
      ·
        refine ⟨3816141116418113166949565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2544094077612075444633043 3816141116418113166949565)
        ·
          refine ⟨1431052918656792437606087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3816141116418113166949565 1431052918656792437606087)
          ·
            refine ⟨2146579377985188656409131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431052918656792437606087 2146579377985188656409131)
            ·
              refine ⟨3219869066977782984613697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146579377985188656409131 3219869066977782984613697)
              ·
                refine ⟨2414901800233337238460273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219869066977782984613697 2414901800233337238460273)
                ·
                  refine ⟨1811176350175002928845205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2414901800233337238460273 1811176350175002928845205)
                  ·
                    refine ⟨84898891414453262289619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1811176350175002928845205 84898891414453262289619)
                    ·
                      rfl

theorem cell22_248010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_248010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248010 prefixEnd_248010 := by exact prefixLift 248010
  have htrace : WordTrace (prefixWord ++ tailWord_248010) baseStart_248010 baseEnd_248010 := by
    simpa [prefixWord, tailWord_248010, baseEnd_248010] using wordTrace_append hprefix tailTrace_248010
  have hstable : (prefixWord ++ tailWord_248010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248010).length < 2 ^ (prefixWord ++ tailWord_248010).sum := by decide
  have hdescent : baseEnd_248010 < baseStart_248010 := by decide
  rcases family_descends (prefixWord ++ tailWord_248010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248110 : List Nat := [4, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_248110 : Nat := 118140960795 + 248110 * 2 ^ 59
def prefixEnd_248110 : Nat := 4983230072969 + 3 ^ 40 * 248110 * 2
def baseEnd_248110 : Nat := 28311041152695444929771

theorem tailTrace_248110 : CollatzResearch.WordTrace tailWord_248110 prefixEnd_248110 28311041152695444929771 := by
  unfold tailWord_248110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1131164391393414832444723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6032876754098212439705189 1131164391393414832444723)
  ·
    refine ⟨1696746587090122248667085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1131164391393414832444723 1696746587090122248667085)
    ·
      refine ⟨636279970158795843250157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1696746587090122248667085 636279970158795843250157)
      ·
        refine ⟨238604988809548441218809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 636279970158795843250157 238604988809548441218809)
        ·
          refine ⟨178953741607161330914107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238604988809548441218809 178953741607161330914107)
          ·
            refine ⟨268430612410741996371161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178953741607161330914107 268430612410741996371161)
            ·
              refine ⟨201322959308056497278371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268430612410741996371161 201322959308056497278371)
              ·
                refine ⟨301984438962084745917557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201322959308056497278371 301984438962084745917557)
                ·
                  refine ⟨28311041152695444929771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301984438962084745917557 28311041152695444929771)
                  ·
                    rfl

theorem cell22_248110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_248110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248110 prefixEnd_248110 := by exact prefixLift 248110
  have htrace : WordTrace (prefixWord ++ tailWord_248110) baseStart_248110 baseEnd_248110 := by
    simpa [prefixWord, tailWord_248110, baseEnd_248110] using wordTrace_append hprefix tailTrace_248110
  have hstable : (prefixWord ++ tailWord_248110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248110).length < 2 ^ (prefixWord ++ tailWord_248110).sum := by decide
  have hdescent : baseEnd_248110 < baseStart_248110 := by decide
  rcases family_descends (prefixWord ++ tailWord_248110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248117 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_248117 : Nat := 118140960795 + 248117 * 2 ^ 59
def prefixEnd_248117 : Nat := 4983230072969 + 3 ^ 40 * 248117 * 2
def baseEnd_248117 : Nat := 84935519701140649864291

theorem tailTrace_248117 : CollatzResearch.WordTrace tailWord_248117 prefixEnd_248117 84935519701140649864291 := by
  unfold tailWord_248117
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049570442121958855062605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6033046961414639236708403 9049570442121958855062605)
  ·
    refine ⟨3393588915795734570648477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9049570442121958855062605 3393588915795734570648477)
    ·
      refine ⟨1272595843423400463993179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3393588915795734570648477 1272595843423400463993179)
      ·
        refine ⟨1908893765135100695989769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272595843423400463993179 1908893765135100695989769)
        ·
          refine ⟨1431670323851325521992327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1908893765135100695989769 1431670323851325521992327)
          ·
            refine ⟨2147505485776988282988491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431670323851325521992327 2147505485776988282988491)
            ·
              refine ⟨3221258228665482424482737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147505485776988282988491 3221258228665482424482737)
              ·
                refine ⟨2415943671499111818362053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3221258228665482424482737 2415943671499111818362053)
                ·
                  refine ⟨452989438406083465942885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2415943671499111818362053 452989438406083465942885)
                  ·
                    refine ⟨84935519701140649864291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 452989438406083465942885 84935519701140649864291)
                    ·
                      rfl

theorem cell22_248117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_248117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248117 prefixEnd_248117 := by exact prefixLift 248117
  have htrace : WordTrace (prefixWord ++ tailWord_248117) baseStart_248117 baseEnd_248117 := by
    simpa [prefixWord, tailWord_248117, baseEnd_248117] using wordTrace_append hprefix tailTrace_248117
  have hstable : (prefixWord ++ tailWord_248117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248117).length < 2 ^ (prefixWord ++ tailWord_248117).sum := by decide
  have hdescent : baseEnd_248117 < baseStart_248117 := by decide
  rcases family_descends (prefixWord ++ tailWord_248117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248147 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 7, 3]
def baseStart_248147 : Nat := 118140960795 + 248147 * 2 ^ 59
def prefixEnd_248147 : Nat := 4983230072969 + 3 ^ 40 * 248147 * 2
def baseEnd_248147 : Nat := 84945789314230571614199

theorem tailTrace_248147 : CollatzResearch.WordTrace tailWord_248147 prefixEnd_248147 84945789314230571614199 := by
  unfold tailWord_248147
  simp only [CollatzResearch.WordTrace]
  refine ⟨9050664632013273978654695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6033776421342182652436463 9050664632013273978654695)
  ·
    refine ⟨13575996948019910967982043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9050664632013273978654695 13575996948019910967982043)
    ·
      refine ⟨20363995422029866451973065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13575996948019910967982043 20363995422029866451973065)
      ·
        refine ⟨15272996566522399838979799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20363995422029866451973065 15272996566522399838979799)
        ·
          refine ⟨22909494849783599758469699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15272996566522399838979799 22909494849783599758469699)
          ·
            refine ⟨34364242274675399637704549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22909494849783599758469699 34364242274675399637704549)
            ·
              refine ⟨6443295426501637432069603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34364242274675399637704549 6443295426501637432069603)
              ·
                refine ⟨9664943139752456148104405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6443295426501637432069603 9664943139752456148104405)
                ·
                  refine ⟨226522104837948190971197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9664943139752456148104405 226522104837948190971197)
                  ·
                    refine ⟨84945789314230571614199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 226522104837948190971197 84945789314230571614199)
                    ·
                      rfl

theorem cell22_248147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 3].length) (baseStart_248147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248147 prefixEnd_248147 := by exact prefixLift 248147
  have htrace : WordTrace (prefixWord ++ tailWord_248147) baseStart_248147 baseEnd_248147 := by
    simpa [prefixWord, tailWord_248147, baseEnd_248147] using wordTrace_append hprefix tailTrace_248147
  have hstable : (prefixWord ++ tailWord_248147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248147).length < 2 ^ (prefixWord ++ tailWord_248147).sum := by decide
  have hdescent : baseEnd_248147 < baseStart_248147 := by decide
  rcases family_descends (prefixWord ++ tailWord_248147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248164 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_248164 : Nat := 118140960795 + 248164 * 2 ^ 59
def prefixEnd_248164 : Nat := 4983230072969 + 3 ^ 40 * 248164 * 2
def baseEnd_248164 : Nat := 84951608761648193939147

theorem tailTrace_248164 : CollatzResearch.WordTrace tailWord_248164 prefixEnd_248164 84951608761648193939147 := by
  unfold tailWord_248164
  simp only [CollatzResearch.WordTrace]
  refine ⟨4525642336475842941011773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6034189781967790588015697 4525642336475842941011773)
  ·
    refine ⟨1697115876178441102879415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4525642336475842941011773 1697115876178441102879415)
    ·
      refine ⟨2545673814267661654319123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1697115876178441102879415 2545673814267661654319123)
      ·
        refine ⟨3818510721401492481478685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2545673814267661654319123 3818510721401492481478685)
        ·
          refine ⟨1431941520525559680554507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3818510721401492481478685 1431941520525559680554507)
          ·
            refine ⟨2147912280788339520831761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431941520525559680554507 2147912280788339520831761)
            ·
              refine ⟨1610934210591254640623821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147912280788339520831761 1610934210591254640623821)
              ·
                refine ⟨604100328971720490233933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1610934210591254640623821 604100328971720490233933)
                ·
                  refine ⟨226537623364395183837725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604100328971720490233933 226537623364395183837725)
                  ·
                    refine ⟨84951608761648193939147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 226537623364395183837725 84951608761648193939147)
                    ·
                      rfl

theorem cell22_248164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_248164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248164 prefixEnd_248164 := by exact prefixLift 248164
  have htrace : WordTrace (prefixWord ++ tailWord_248164) baseStart_248164 baseEnd_248164 := by
    simpa [prefixWord, tailWord_248164, baseEnd_248164] using wordTrace_append hprefix tailTrace_248164
  have hstable : (prefixWord ++ tailWord_248164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248164).length < 2 ^ (prefixWord ++ tailWord_248164).sum := by decide
  have hdescent : baseEnd_248164 < baseStart_248164 := by decide
  rcases family_descends (prefixWord ++ tailWord_248164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248181 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 3, 3]
def baseStart_248181 : Nat := 118140960795 + 248181 * 2 ^ 59
def prefixEnd_248181 : Nat := 4983230072969 + 3 ^ 40 * 248181 * 2
def baseEnd_248181 : Nat := 84957428209065816264095

theorem tailTrace_248181 : CollatzResearch.WordTrace tailWord_248181 prefixEnd_248181 84957428209065816264095 := by
  unfold tailWord_248181
  simp only [CollatzResearch.WordTrace]
  refine ⟨9051904713890097785392397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6034603142593398523594931 9051904713890097785392397)
  ·
    refine ⟨3394464267708786669522149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9051904713890097785392397 3394464267708786669522149)
    ·
      refine ⟨636462050195397500535403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3394464267708786669522149 636462050195397500535403)
      ·
        refine ⟨954693075293096250803105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636462050195397500535403 954693075293096250803105)
        ·
          refine ⟨716019806469822188102329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 954693075293096250803105 716019806469822188102329)
          ·
            refine ⟨537014854852366641076747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716019806469822188102329 537014854852366641076747)
            ·
              refine ⟨805522282278549961615121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537014854852366641076747 805522282278549961615121)
              ·
                refine ⟨604141711708912471211341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 805522282278549961615121 604141711708912471211341)
                ·
                  refine ⟨226553141890842176704253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604141711708912471211341 226553141890842176704253)
                  ·
                    refine ⟨84957428209065816264095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 226553141890842176704253 84957428209065816264095)
                    ·
                      rfl

theorem cell22_248181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_248181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248181 prefixEnd_248181 := by exact prefixLift 248181
  have htrace : WordTrace (prefixWord ++ tailWord_248181) baseStart_248181 baseEnd_248181 := by
    simpa [prefixWord, tailWord_248181, baseEnd_248181] using wordTrace_append hprefix tailTrace_248181
  have hstable : (prefixWord ++ tailWord_248181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248181).length < 2 ^ (prefixWord ++ tailWord_248181).sum := by decide
  have hdescent : baseEnd_248181 < baseStart_248181 := by decide
  rcases family_descends (prefixWord ++ tailWord_248181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248241 : List Nat := [1, 2, 2, 4, 1, 3, 2, 2, 1, 4]
def baseStart_248241 : Nat := 118140960795 + 248241 * 2 ^ 59
def prefixEnd_248241 : Nat := 4983230072969 + 3 ^ 40 * 248241 * 2
def baseEnd_248241 : Nat := 84977967435245659763911

theorem tailTrace_248241 : CollatzResearch.WordTrace tailWord_248241 prefixEnd_248241 84977967435245659763911 := by
  unfold tailWord_248241
  simp only [CollatzResearch.WordTrace]
  refine ⟨9054093093672728032576577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6036062062448485355051051 9054093093672728032576577)
  ·
    refine ⟨6790569820254546024432433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9054093093672728032576577 6790569820254546024432433)
    ·
      refine ⟨5092927365190909518324325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6790569820254546024432433 5092927365190909518324325)
      ·
        refine ⟨954923880973295534685811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5092927365190909518324325 954923880973295534685811)
        ·
          refine ⟨1432385821459943302028717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954923880973295534685811 1432385821459943302028717)
          ·
            refine ⟨537144683047478738260769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1432385821459943302028717 537144683047478738260769)
            ·
              refine ⟨402858512285609053695577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537144683047478738260769 402858512285609053695577)
              ·
                refine ⟨302143884214206790271683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402858512285609053695577 302143884214206790271683)
                ·
                  refine ⟨453215826321310185407525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302143884214206790271683 453215826321310185407525)
                  ·
                    refine ⟨84977967435245659763911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453215826321310185407525 84977967435245659763911)
                    ·
                      rfl

theorem cell22_248241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_248241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248241 prefixEnd_248241 := by exact prefixLift 248241
  have htrace : WordTrace (prefixWord ++ tailWord_248241) baseStart_248241 baseEnd_248241 := by
    simpa [prefixWord, tailWord_248241, baseEnd_248241] using wordTrace_append hprefix tailTrace_248241
  have hstable : (prefixWord ++ tailWord_248241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248241).length < 2 ^ (prefixWord ++ tailWord_248241).sum := by decide
  have hdescent : baseEnd_248241 < baseStart_248241 := by decide
  rcases family_descends (prefixWord ++ tailWord_248241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248254 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_248254 : Nat := 118140960795 + 248254 * 2 ^ 59
def prefixEnd_248254 : Nat := 4983230072969 + 3 ^ 40 * 248254 * 2
def baseEnd_248254 : Nat := 84982417600917959188871

theorem tailTrace_248254 : CollatzResearch.WordTrace tailWord_248254 prefixEnd_248254 84982417600917959188871 := by
  unfold tailWord_248254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1131820905328203906599977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6036378161750420835199877 1131820905328203906599977)
  ·
    refine ⟨848865678996152929949983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1131820905328203906599977 848865678996152929949983)
    ·
      refine ⟨1273298518494229394924975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 848865678996152929949983 1273298518494229394924975)
      ·
        refine ⟨1909947777741344092387463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273298518494229394924975 1909947777741344092387463)
        ·
          refine ⟨2864921666612016138581195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909947777741344092387463 2864921666612016138581195)
          ·
            refine ⟨4297382499918024207871793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864921666612016138581195 4297382499918024207871793)
            ·
              refine ⟨3223036874938518155903845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4297382499918024207871793 3223036874938518155903845)
              ·
                refine ⟨604319414050972154231971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3223036874938518155903845 604319414050972154231971)
                ·
                  refine ⟨906479121076458231347957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604319414050972154231971 906479121076458231347957)
                  ·
                    refine ⟨84982417600917959188871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 906479121076458231347957 84982417600917959188871)
                    ·
                      rfl

theorem cell22_248254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_248254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248254 prefixEnd_248254 := by exact prefixLift 248254
  have htrace : WordTrace (prefixWord ++ tailWord_248254) baseStart_248254 baseEnd_248254 := by
    simpa [prefixWord, tailWord_248254, baseEnd_248254] using wordTrace_append hprefix tailTrace_248254
  have hstable : (prefixWord ++ tailWord_248254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248254).length < 2 ^ (prefixWord ++ tailWord_248254).sum := by decide
  have hdescent : baseEnd_248254 < baseStart_248254 := by decide
  rcases family_descends (prefixWord ++ tailWord_248254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248297 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 4, 6]
def baseStart_248297 : Nat := 118140960795 + 248297 * 2 ^ 59
def prefixEnd_248297 : Nat := 4983230072969 + 3 ^ 40 * 248297 * 2
def baseEnd_248297 : Nat := 84997137379680180363739

theorem tailTrace_248297 : CollatzResearch.WordTrace tailWord_248297 prefixEnd_248297 84997137379680180363739 := by
  unfold tailWord_248297
  simp only [CollatzResearch.WordTrace]
  refine ⟨9056135581469849596615145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6037423720979899731076763 9056135581469849596615145)
  ·
    refine ⟨6792101686102387197461359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9056135581469849596615145 6792101686102387197461359)
    ·
      refine ⟨10188152529153580796192039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6792101686102387197461359 10188152529153580796192039)
      ·
        refine ⟨15282228793730371194288059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10188152529153580796192039 15282228793730371194288059)
        ·
          refine ⟨22923343190595556791432089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15282228793730371194288059 22923343190595556791432089)
          ·
            refine ⟨17192507392946667593574067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22923343190595556791432089 17192507392946667593574067)
            ·
              refine ⟨25788761089420001390361101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17192507392946667593574067 25788761089420001390361101)
              ·
                refine ⟨9670785408532500521385413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25788761089420001390361101 9670785408532500521385413)
                ·
                  refine ⟨1813272264099843847759765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9670785408532500521385413 1813272264099843847759765)
                  ·
                    refine ⟨84997137379680180363739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1813272264099843847759765 84997137379680180363739)
                    ·
                      rfl

theorem cell22_248297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_248297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248297 prefixEnd_248297 := by exact prefixLift 248297
  have htrace : WordTrace (prefixWord ++ tailWord_248297) baseStart_248297 baseEnd_248297 := by
    simpa [prefixWord, tailWord_248297, baseEnd_248297] using wordTrace_append hprefix tailTrace_248297
  have hstable : (prefixWord ++ tailWord_248297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248297).length < 2 ^ (prefixWord ++ tailWord_248297).sum := by decide
  have hdescent : baseEnd_248297 < baseStart_248297 := by decide
  rcases family_descends (prefixWord ++ tailWord_248297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248299 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 5, 3]
def baseStart_248299 : Nat := 118140960795 + 248299 * 2 ^ 59
def prefixEnd_248299 : Nat := 4983230072969 + 3 ^ 40 * 248299 * 2
def baseEnd_248299 : Nat := 84997822020552841813733

theorem tailTrace_248299 : CollatzResearch.WordTrace tailWord_248299 prefixEnd_248299 84997822020552841813733 := by
  unfold tailWord_248299
  simp only [CollatzResearch.WordTrace]
  refine ⟨9056208527462603938187951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6037472351641735958791967 9056208527462603938187951)
  ·
    refine ⟨13584312791193905907281927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9056208527462603938187951 13584312791193905907281927)
    ·
      refine ⟨20376469186790858860922891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13584312791193905907281927 20376469186790858860922891)
      ·
        refine ⟨30564703780186288291384337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20376469186790858860922891 30564703780186288291384337)
        ·
          refine ⟨22923527835139716218538253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30564703780186288291384337 22923527835139716218538253)
          ·
            refine ⟨8596322938177393581951845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22923527835139716218538253 8596322938177393581951845)
            ·
              refine ⟨1611810550908261296615971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8596322938177393581951845 1611810550908261296615971)
              ·
                refine ⟨2417715826362391944923957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611810550908261296615971 2417715826362391944923957)
                ·
                  refine ⟨226660858721474244836621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2417715826362391944923957 226660858721474244836621)
                  ·
                    refine ⟨84997822020552841813733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 226660858721474244836621 84997822020552841813733)
                    ·
                      rfl

theorem cell22_248299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 3].length) (baseStart_248299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248299 prefixEnd_248299 := by exact prefixLift 248299
  have htrace : WordTrace (prefixWord ++ tailWord_248299) baseStart_248299 baseEnd_248299 := by
    simpa [prefixWord, tailWord_248299, baseEnd_248299] using wordTrace_append hprefix tailTrace_248299
  have hstable : (prefixWord ++ tailWord_248299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248299).length < 2 ^ (prefixWord ++ tailWord_248299).sum := by decide
  have hdescent : baseEnd_248299 < baseStart_248299 := by decide
  rcases family_descends (prefixWord ++ tailWord_248299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248344 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 1, 7]
def baseStart_248344 : Nat := 118140960795 + 248344 * 2 ^ 59
def prefixEnd_248344 : Nat := 4983230072969 + 3 ^ 40 * 248344 * 2
def baseEnd_248344 : Nat := 85013226440187724438595

theorem tailTrace_248344 : CollatzResearch.WordTrace tailWord_248344 prefixEnd_248344 85013226440187724438595 := by
  unfold tailWord_248344
  simp only [CollatzResearch.WordTrace]
  refine ⟨4528924906149788311788043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6038566541533051082384057 4528924906149788311788043)
  ·
    refine ⟨6793387359224682467682065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4528924906149788311788043 6793387359224682467682065)
    ·
      refine ⟨5095040519418511850761549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6793387359224682467682065 5095040519418511850761549)
      ·
        refine ⟨1910640194781941944035581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5095040519418511850761549 1910640194781941944035581)
        ·
          refine ⟨716490073043228229013343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1910640194781941944035581 716490073043228229013343)
          ·
            refine ⟨1074735109564842343520015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716490073043228229013343 1074735109564842343520015)
            ·
              refine ⟨1612102664347263515280023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074735109564842343520015 1612102664347263515280023)
              ·
                refine ⟨2418153996520895272920035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612102664347263515280023 2418153996520895272920035)
                ·
                  refine ⟨3627230994781342909380053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418153996520895272920035 3627230994781342909380053)
                  ·
                    refine ⟨85013226440187724438595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3627230994781342909380053 85013226440187724438595)
                    ·
                      rfl

theorem cell22_248344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_248344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248344 prefixEnd_248344 := by exact prefixLift 248344
  have htrace : WordTrace (prefixWord ++ tailWord_248344) baseStart_248344 baseEnd_248344 := by
    simpa [prefixWord, tailWord_248344, baseEnd_248344] using wordTrace_append hprefix tailTrace_248344
  have hstable : (prefixWord ++ tailWord_248344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248344).length < 2 ^ (prefixWord ++ tailWord_248344).sum := by decide
  have hdescent : baseEnd_248344 < baseStart_248344 := by decide
  rcases family_descends (prefixWord ++ tailWord_248344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248376 : List Nat := [2, 1, 2, 1, 4, 1, 3, 3, 1, 4]
def baseStart_248376 : Nat := 118140960795 + 248376 * 2 ^ 59
def prefixEnd_248376 : Nat := 4983230072969 + 3 ^ 40 * 248376 * 2
def baseEnd_248376 : Nat := 85024180694150307638497

theorem tailTrace_248376 : CollatzResearch.WordTrace tailWord_248376 prefixEnd_248376 85024180694150307638497 := by
  unfold tailWord_248376
  simp only [CollatzResearch.WordTrace]
  refine ⟨4529508474091823044370491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6039344632122430725827321 4529508474091823044370491)
  ·
    refine ⟨6794262711137734566555737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4529508474091823044370491 6794262711137734566555737)
    ·
      refine ⟨5095697033353300924916803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6794262711137734566555737 5095697033353300924916803)
      ·
        refine ⟨7643545550029951387375205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5095697033353300924916803 7643545550029951387375205)
        ·
          refine ⟨1433164790630615885132851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7643545550029951387375205 1433164790630615885132851)
          ·
            refine ⟨2149747185945923827699277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433164790630615885132851 2149747185945923827699277)
            ·
              refine ⟨806155194729721435387229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2149747185945923827699277 806155194729721435387229)
              ·
                refine ⟨302308198023645538270211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 806155194729721435387229 302308198023645538270211)
                ·
                  refine ⟨453462297035468307405317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302308198023645538270211 453462297035468307405317)
                  ·
                    refine ⟨85024180694150307638497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453462297035468307405317 85024180694150307638497)
                    ·
                      rfl

theorem cell22_248376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_248376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248376 prefixEnd_248376 := by exact prefixLift 248376
  have htrace : WordTrace (prefixWord ++ tailWord_248376) baseStart_248376 baseEnd_248376 := by
    simpa [prefixWord, tailWord_248376, baseEnd_248376] using wordTrace_append hprefix tailTrace_248376
  have hstable : (prefixWord ++ tailWord_248376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248376).length < 2 ^ (prefixWord ++ tailWord_248376).sum := by decide
  have hdescent : baseEnd_248376 < baseStart_248376 := by decide
  rcases family_descends (prefixWord ++ tailWord_248376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248391 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 6]
def baseStart_248391 : Nat := 118140960795 + 248391 * 2 ^ 59
def prefixEnd_248391 : Nat := 4983230072969 + 3 ^ 40 * 248391 * 2
def baseEnd_248391 : Nat := 28343105166898422837817

theorem tailTrace_248391 : CollatzResearch.WordTrace tailWord_248391 prefixEnd_248391 28343105166898422837817 := by
  unfold tailWord_248391
  simp only [CollatzResearch.WordTrace]
  refine ⟨9059564043129303650537027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6039709362086202433691351 9059564043129303650537027)
  ·
    refine ⟨13589346064693955475805541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9059564043129303650537027 13589346064693955475805541)
    ·
      refine ⟨2548002387130116651713539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13589346064693955475805541 2548002387130116651713539)
      ·
        refine ⟨3822003580695174977570309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2548002387130116651713539 3822003580695174977570309)
        ·
          refine ⟨716625671380345308294433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3822003580695174977570309 716625671380345308294433)
          ·
            refine ⟨537469253535258981220825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716625671380345308294433 537469253535258981220825)
            ·
              refine ⟨403101940151444235915619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537469253535258981220825 403101940151444235915619)
              ·
                refine ⟨604652910227166353873429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403101940151444235915619 604652910227166353873429)
                ·
                  refine ⟨28343105166898422837817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 604652910227166353873429 28343105166898422837817)
                  ·
                    rfl

theorem cell22_248391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 6].length) (baseStart_248391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248391 prefixEnd_248391 := by exact prefixLift 248391
  have htrace : WordTrace (prefixWord ++ tailWord_248391) baseStart_248391 baseEnd_248391 := by
    simpa [prefixWord, tailWord_248391, baseEnd_248391] using wordTrace_append hprefix tailTrace_248391
  have hstable : (prefixWord ++ tailWord_248391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248391).length < 2 ^ (prefixWord ++ tailWord_248391).sum := by decide
  have hdescent : baseEnd_248391 < baseStart_248391 := by decide
  rcases family_descends (prefixWord ++ tailWord_248391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248419 : List Nat := [1, 1, 1, 5, 1, 2, 3, 8]
def baseStart_248419 : Nat := 118140960795 + 248419 * 2 ^ 59
def prefixEnd_248419 : Nat := 4983230072969 + 3 ^ 40 * 248419 * 2
def baseEnd_248419 : Nat := 9448766719212503201485

theorem tailTrace_248419 : CollatzResearch.WordTrace tailWord_248419 prefixEnd_248419 9448766719212503201485 := by
  unfold tailWord_248419
  simp only [CollatzResearch.WordTrace]
  refine ⟨9060585287027864432556311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6040390191351909621704207 9060585287027864432556311)
  ·
    refine ⟨13590877930541796648834467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9060585287027864432556311 13590877930541796648834467)
    ·
      refine ⟨20386316895812694973251701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13590877930541796648834467 20386316895812694973251701)
      ·
        refine ⟨1911217208982440153742347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20386316895812694973251701 1911217208982440153742347)
        ·
          refine ⟨2866825813473660230613521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911217208982440153742347 2866825813473660230613521)
          ·
            refine ⟨2150119360105245172960141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2866825813473660230613521 2150119360105245172960141)
            ·
              refine ⟨806294760039466939860053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2150119360105245172960141 806294760039466939860053)
              ·
                refine ⟨9448766719212503201485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 806294760039466939860053 9448766719212503201485)
                ·
                  rfl

theorem cell22_248419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 8].length) (baseStart_248419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248419 prefixEnd_248419 := by exact prefixLift 248419
  have htrace : WordTrace (prefixWord ++ tailWord_248419) baseStart_248419 baseEnd_248419 := by
    simpa [prefixWord, tailWord_248419, baseEnd_248419] using wordTrace_append hprefix tailTrace_248419
  have hstable : (prefixWord ++ tailWord_248419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248419).length < 2 ^ (prefixWord ++ tailWord_248419).sum := by decide
  have hdescent : baseEnd_248419 < baseStart_248419 := by decide
  rcases family_descends (prefixWord ++ tailWord_248419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248511 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 3, 4]
def baseStart_248511 : Nat := 118140960795 + 248511 * 2 ^ 59
def prefixEnd_248511 : Nat := 4983230072969 + 3 ^ 40 * 248511 * 2
def baseEnd_248511 : Nat := 85070393953054955513083

theorem tailTrace_248511 : CollatzResearch.WordTrace tailWord_248511 prefixEnd_248511 85070393953054955513083 := by
  unfold tailWord_248511
  simp only [CollatzResearch.WordTrace]
  refine ⟨9063940802694564144905387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6042627201796376096603591 9063940802694564144905387)
  ·
    refine ⟨13595911204041846217358081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9063940802694564144905387 13595911204041846217358081)
    ·
      refine ⟨10196933403031384663018561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13595911204041846217358081 10196933403031384663018561)
      ·
        refine ⟨7647700052273538497263921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10196933403031384663018561 7647700052273538497263921)
        ·
          refine ⟨5735775039205153872947941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7647700052273538497263921 5735775039205153872947941)
          ·
            refine ⟨1075457819850966351177739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5735775039205153872947941 1075457819850966351177739)
            ·
              refine ⟨1613186729776449526766609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075457819850966351177739 1613186729776449526766609)
              ·
                refine ⟨1209890047332337145074957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1613186729776449526766609 1209890047332337145074957)
                ·
                  refine ⟨453708767749626429403109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209890047332337145074957 453708767749626429403109)
                  ·
                    refine ⟨85070393953054955513083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453708767749626429403109 85070393953054955513083)
                    ·
                      rfl

theorem cell22_248511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_248511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248511 prefixEnd_248511 := by exact prefixLift 248511
  have htrace : WordTrace (prefixWord ++ tailWord_248511) baseStart_248511 baseEnd_248511 := by
    simpa [prefixWord, tailWord_248511, baseEnd_248511] using wordTrace_append hprefix tailTrace_248511
  have hstable : (prefixWord ++ tailWord_248511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248511).length < 2 ^ (prefixWord ++ tailWord_248511).sum := by decide
  have hdescent : baseEnd_248511 < baseStart_248511 := by decide
  rcases family_descends (prefixWord ++ tailWord_248511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248526 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_248526 : Nat := 118140960795 + 248526 * 2 ^ 59
def prefixEnd_248526 : Nat := 4983230072969 + 3 ^ 40 * 248526 * 2
def baseEnd_248526 : Nat := 28358509586533305462679

theorem tailTrace_248526 : CollatzResearch.WordTrace tailWord_248526 prefixEnd_248526 28358509586533305462679 := by
  unfold tailWord_248526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133060987205027713337679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6042991931760147804467621 1133060987205027713337679)
  ·
    refine ⟨1699591480807541570006519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1133060987205027713337679 1699591480807541570006519)
    ·
      refine ⟨2549387221211312355009779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1699591480807541570006519 2549387221211312355009779)
      ·
        refine ⟨3824080831816968532514669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2549387221211312355009779 3824080831816968532514669)
        ·
          refine ⟨1434030311931363199693001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3824080831816968532514669 1434030311931363199693001)
          ·
            refine ⟨1075522733948522399769751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1434030311931363199693001 1075522733948522399769751)
            ·
              refine ⟨1613284100922783599654627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075522733948522399769751 1613284100922783599654627)
              ·
                refine ⟨2419926151384175399481941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613284100922783599654627 2419926151384175399481941)
                ·
                  refine ⟨28358509586533305462679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2419926151384175399481941 28358509586533305462679)
                  ·
                    rfl

theorem cell22_248526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_248526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248526 prefixEnd_248526 := by exact prefixLift 248526
  have htrace : WordTrace (prefixWord ++ tailWord_248526) baseStart_248526 baseEnd_248526 := by
    simpa [prefixWord, tailWord_248526, baseEnd_248526] using wordTrace_append hprefix tailTrace_248526
  have hstable : (prefixWord ++ tailWord_248526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248526).length < 2 ^ (prefixWord ++ tailWord_248526).sum := by decide
  have hdescent : baseEnd_248526 < baseStart_248526 := by decide
  rcases family_descends (prefixWord ++ tailWord_248526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248543 : List Nat := [1, 1, 2, 3, 2, 3, 1, 5, 4]
def baseStart_248543 : Nat := 118140960795 + 248543 * 2 ^ 59
def prefixEnd_248543 : Nat := 4983230072969 + 3 ^ 40 * 248543 * 2
def baseEnd_248543 : Nat := 28360449402339179570995

theorem tailTrace_248543 : CollatzResearch.WordTrace tailWord_248543 prefixEnd_248543 28360449402339179570995 := by
  unfold tailWord_248543
  simp only [CollatzResearch.WordTrace]
  refine ⟨9065107938578633610070283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6043405292385755740046855 9065107938578633610070283)
  ·
    refine ⟨13597661907867950415105425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9065107938578633610070283 13597661907867950415105425)
    ·
      refine ⟨10198246430900962811329069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13597661907867950415105425 10198246430900962811329069)
      ·
        refine ⟨3824342411587861054248401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10198246430900962811329069 3824342411587861054248401)
        ·
          refine ⟨2868256808690895790686301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3824342411587861054248401 2868256808690895790686301)
          ·
            refine ⟨1075596303259085921507363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2868256808690895790686301 1075596303259085921507363)
            ·
              refine ⟨1613394454888628882261045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075596303259085921507363 1613394454888628882261045)
              ·
                refine ⟨151255730145808957711973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1613394454888628882261045 151255730145808957711973)
                ·
                  refine ⟨28360449402339179570995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151255730145808957711973 28360449402339179570995)
                  ·
                    rfl

theorem cell22_248543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 4].length) (baseStart_248543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248543 prefixEnd_248543 := by exact prefixLift 248543
  have htrace : WordTrace (prefixWord ++ tailWord_248543) baseStart_248543 baseEnd_248543 := by
    simpa [prefixWord, tailWord_248543, baseEnd_248543] using wordTrace_append hprefix tailTrace_248543
  have hstable : (prefixWord ++ tailWord_248543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248543).length < 2 ^ (prefixWord ++ tailWord_248543).sum := by decide
  have hdescent : baseEnd_248543 < baseStart_248543 := by decide
  rcases family_descends (prefixWord ++ tailWord_248543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248545 : List Nat := [1, 2, 3, 1, 4, 1, 4, 1, 1, 4]
def baseStart_248545 : Nat := 118140960795 + 248545 * 2 ^ 59
def prefixEnd_248545 : Nat := 4983230072969 + 3 ^ 40 * 248545 * 2
def baseEnd_248545 : Nat := 85082032847890200162979

theorem tailTrace_248545 : CollatzResearch.WordTrace tailWord_248545 prefixEnd_248545 85082032847890200162979 := by
  unfold tailWord_248545
  simp only [CollatzResearch.WordTrace]
  refine ⟨9065180884571387951643089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6043453923047591967762059 9065180884571387951643089)
  ·
    refine ⟨6798885663428540963732317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9065180884571387951643089 6798885663428540963732317)
    ·
      refine ⟨2549582123785702861399619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6798885663428540963732317 2549582123785702861399619)
      ·
        refine ⟨3824373185678554292099429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2549582123785702861399619 3824373185678554292099429)
        ·
          refine ⟨717069972314728929768643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3824373185678554292099429 717069972314728929768643)
          ·
            refine ⟨1075604958472093394652965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717069972314728929768643 1075604958472093394652965)
            ·
              refine ⟨201675929713517511497431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1075604958472093394652965 201675929713517511497431)
              ·
                refine ⟨302513894570276267246147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201675929713517511497431 302513894570276267246147)
                ·
                  refine ⟨453770841855414400869221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302513894570276267246147 453770841855414400869221)
                  ·
                    refine ⟨85082032847890200162979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453770841855414400869221 85082032847890200162979)
                    ·
                      rfl

theorem cell22_248545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_248545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248545 prefixEnd_248545 := by exact prefixLift 248545
  have htrace : WordTrace (prefixWord ++ tailWord_248545) baseStart_248545 baseEnd_248545 := by
    simpa [prefixWord, tailWord_248545, baseEnd_248545] using wordTrace_append hprefix tailTrace_248545
  have hstable : (prefixWord ++ tailWord_248545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248545).length < 2 ^ (prefixWord ++ tailWord_248545).sum := by decide
  have hdescent : baseEnd_248545 < baseStart_248545 := by decide
  rcases family_descends (prefixWord ++ tailWord_248545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248556 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_248556 : Nat := 118140960795 + 248556 * 2 ^ 59
def prefixEnd_248556 : Nat := 4983230072969 + 3 ^ 40 * 248556 * 2
def baseEnd_248556 : Nat := 85085798372689838137945

theorem tailTrace_248556 : CollatzResearch.WordTrace tailWord_248556 prefixEnd_248556 85085798372689838137945 := by
  unfold tailWord_248556
  simp only [CollatzResearch.WordTrace]
  refine ⟨4532791043765768415146761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6043721391687691220195681 4532791043765768415146761)
  ·
    refine ⟨3399593282824326311360071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4532791043765768415146761 3399593282824326311360071)
    ·
      refine ⟨5099389924236489467040107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3399593282824326311360071 5099389924236489467040107)
      ·
        refine ⟨7649084886354734200560161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5099389924236489467040107 7649084886354734200560161)
        ·
          refine ⟨5736813664766050650420121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7649084886354734200560161 5736813664766050650420121)
          ·
            refine ⟨4302610248574537987815091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5736813664766050650420121 4302610248574537987815091)
            ·
              refine ⟨6453915372861806981722637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4302610248574537987815091 6453915372861806981722637)
              ·
                refine ⟨2420218264823177618145989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6453915372861806981722637 2420218264823177618145989)
                ·
                  refine ⟨453790924654345803402373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2420218264823177618145989 453790924654345803402373)
                  ·
                    refine ⟨85085798372689838137945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453790924654345803402373 85085798372689838137945)
                    ·
                      rfl

theorem cell22_248556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_248556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248556 prefixEnd_248556 := by exact prefixLift 248556
  have htrace : WordTrace (prefixWord ++ tailWord_248556) baseStart_248556 baseEnd_248556 := by
    simpa [prefixWord, tailWord_248556, baseEnd_248556] using wordTrace_append hprefix tailTrace_248556
  have hstable : (prefixWord ++ tailWord_248556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248556).length < 2 ^ (prefixWord ++ tailWord_248556).sum := by decide
  have hdescent : baseEnd_248556 < baseStart_248556 := by decide
  rcases family_descends (prefixWord ++ tailWord_248556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248586 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_248586 : Nat := 118140960795 + 248586 * 2 ^ 59
def prefixEnd_248586 : Nat := 4983230072969 + 3 ^ 40 * 248586 * 2
def baseEnd_248586 : Nat := 85096067985779759887853

theorem tailTrace_248586 : CollatzResearch.WordTrace tailWord_248586 prefixEnd_248586 85096067985779759887853 := by
  unfold tailWord_248586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266669069355712988471403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6044450851615234635923741 2266669069355712988471403)
  ·
    refine ⟨3400003604033569482707105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2266669069355712988471403 3400003604033569482707105)
    ·
      refine ⟨2550002703025177112030329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3400003604033569482707105 2550002703025177112030329)
      ·
        refine ⟨1912502027268882834022747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2550002703025177112030329 1912502027268882834022747)
        ·
          refine ⟨2868753040903324251034121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912502027268882834022747 2868753040903324251034121)
          ·
            refine ⟨2151564780677493188275591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2868753040903324251034121 2151564780677493188275591)
            ·
              refine ⟨3227347171016239782413387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151564780677493188275591 3227347171016239782413387)
              ·
                refine ⟨4841020756524359673620081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3227347171016239782413387 4841020756524359673620081)
                ·
                  refine ⟨3630765567393269755215061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4841020756524359673620081 3630765567393269755215061)
                  ·
                    refine ⟨85096067985779759887853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3630765567393269755215061 85096067985779759887853)
                    ·
                      rfl

theorem cell22_248586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_248586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248586 prefixEnd_248586 := by exact prefixLift 248586
  have htrace : WordTrace (prefixWord ++ tailWord_248586) baseStart_248586 baseEnd_248586 := by
    simpa [prefixWord, tailWord_248586, baseEnd_248586] using wordTrace_append hprefix tailTrace_248586
  have hstable : (prefixWord ++ tailWord_248586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248586).length < 2 ^ (prefixWord ++ tailWord_248586).sum := by decide
  have hdescent : baseEnd_248586 < baseStart_248586 := by decide
  rcases family_descends (prefixWord ++ tailWord_248586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248594 : List Nat := [3, 2, 4, 1, 2, 2, 1, 3, 4]
def baseStart_248594 : Nat := 118140960795 + 248594 * 2 ^ 59
def prefixEnd_248594 : Nat := 4983230072969 + 3 ^ 40 * 248594 * 2
def baseEnd_248594 : Nat := 28366268849756801895943

theorem tailTrace_248594 : CollatzResearch.WordTrace tailWord_248594 prefixEnd_248594 28366268849756801895943 := by
  unfold tailWord_248594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266742015348467330044209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6044645374262579546784557 2266742015348467330044209)
  ·
    refine ⟨1700056511511350497533157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2266742015348467330044209 1700056511511350497533157)
    ·
      refine ⟨318760595908378218287467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1700056511511350497533157 318760595908378218287467)
      ·
        refine ⟨478140893862567327431201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318760595908378218287467 478140893862567327431201)
        ·
          refine ⟨358605670396925495573401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478140893862567327431201 358605670396925495573401)
          ·
            refine ⟨268954252797694121680051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358605670396925495573401 268954252797694121680051)
            ·
              refine ⟨403431379196541182520077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268954252797694121680051 403431379196541182520077)
              ·
                refine ⟨151286767198702943445029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403431379196541182520077 151286767198702943445029)
                ·
                  refine ⟨28366268849756801895943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151286767198702943445029 28366268849756801895943)
                  ·
                    rfl

theorem cell22_248594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_248594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248594 prefixEnd_248594 := by exact prefixLift 248594
  have htrace : WordTrace (prefixWord ++ tailWord_248594) baseStart_248594 baseEnd_248594 := by
    simpa [prefixWord, tailWord_248594, baseEnd_248594] using wordTrace_append hprefix tailTrace_248594
  have hstable : (prefixWord ++ tailWord_248594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248594).length < 2 ^ (prefixWord ++ tailWord_248594).sum := by decide
  have hdescent : baseEnd_248594 < baseStart_248594 := by decide
  rcases family_descends (prefixWord ++ tailWord_248594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248605 : List Nat := [1, 4, 2, 4, 1, 2, 8]
def baseStart_248605 : Nat := 118140960795 + 248605 * 2 ^ 59
def prefixEnd_248605 : Nat := 4983230072969 + 3 ^ 40 * 248605 * 2
def baseEnd_248605 : Nat := 3151947113854446061585

theorem tailTrace_248605 : CollatzResearch.WordTrace tailWord_248605 prefixEnd_248605 3151947113854446061585 := by
  unfold tailWord_248605
  simp only [CollatzResearch.WordTrace]
  refine ⟨9067369264354018198827269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6044912842902678799218179 9067369264354018198827269)
  ·
    refine ⟨1700131737066378412280113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9067369264354018198827269 1700131737066378412280113)
    ·
      refine ⟨1275098802799783809210085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1700131737066378412280113 1275098802799783809210085)
      ·
        refine ⟨239081025524959464226891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1275098802799783809210085 239081025524959464226891)
        ·
          refine ⟨358621538287439196340337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239081025524959464226891 358621538287439196340337)
          ·
            refine ⟨268966153715579397255253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358621538287439196340337 268966153715579397255253)
            ·
              refine ⟨3151947113854446061585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 268966153715579397255253 3151947113854446061585)
              ·
                rfl

theorem cell22_248605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 8].length) (baseStart_248605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248605 prefixEnd_248605 := by exact prefixLift 248605
  have htrace : WordTrace (prefixWord ++ tailWord_248605) baseStart_248605 baseEnd_248605 := by
    simpa [prefixWord, tailWord_248605, baseEnd_248605] using wordTrace_append hprefix tailTrace_248605
  have hstable : (prefixWord ++ tailWord_248605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248605).length < 2 ^ (prefixWord ++ tailWord_248605).sum := by decide
  have hdescent : baseEnd_248605 < baseStart_248605 := by decide
  rcases family_descends (prefixWord ++ tailWord_248605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248631 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 1, 7]
def baseStart_248631 : Nat := 118140960795 + 248631 * 2 ^ 59
def prefixEnd_248631 : Nat := 4983230072969 + 3 ^ 40 * 248631 * 2
def baseEnd_248631 : Nat := 85111472405414642512715

theorem tailTrace_248631 : CollatzResearch.WordTrace tailWord_248631 prefixEnd_248631 85111472405414642512715 := by
  unfold tailWord_248631
  simp only [CollatzResearch.WordTrace]
  refine ⟨9068317562259824639273747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6045545041506549759515831 9068317562259824639273747)
  ·
    refine ⟨13602476343389736958910621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9068317562259824639273747 13602476343389736958910621)
    ·
      refine ⟨5100928628771151359591483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13602476343389736958910621 5100928628771151359591483)
      ·
        refine ⟨7651392943156727039387225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5100928628771151359591483 7651392943156727039387225)
        ·
          refine ⟨5738544707367545279540419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7651392943156727039387225 5738544707367545279540419)
          ·
            refine ⟨8607817061051317919310629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5738544707367545279540419 8607817061051317919310629)
            ·
              refine ⟨1613965698947122109870743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8607817061051317919310629 1613965698947122109870743)
              ·
                refine ⟨2420948548420683164806115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613965698947122109870743 2420948548420683164806115)
                ·
                  refine ⟨3631422822631024747209173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420948548420683164806115 3631422822631024747209173)
                  ·
                    refine ⟨85111472405414642512715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3631422822631024747209173 85111472405414642512715)
                    ·
                      rfl

theorem cell22_248631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_248631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248631 prefixEnd_248631 := by exact prefixLift 248631
  have htrace : WordTrace (prefixWord ++ tailWord_248631) baseStart_248631 baseEnd_248631 := by
    simpa [prefixWord, tailWord_248631, baseEnd_248631] using wordTrace_append hprefix tailTrace_248631
  have hstable : (prefixWord ++ tailWord_248631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248631).length < 2 ^ (prefixWord ++ tailWord_248631).sum := by decide
  have hdescent : baseEnd_248631 < baseStart_248631 := by decide
  rcases family_descends (prefixWord ++ tailWord_248631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248712 : List Nat := [2, 1, 3, 3, 2, 2, 2, 3, 4]
def baseStart_248712 : Nat := 118140960795 + 248712 * 2 ^ 59
def prefixEnd_248712 : Nat := 4983230072969 + 3 ^ 40 * 248712 * 2
def baseEnd_248712 : Nat := 28379733453585810412489

theorem tailTrace_248712 : CollatzResearch.WordTrace tailWord_248712 prefixEnd_248712 28379733453585810412489 := by
  unfold tailWord_248712
  simp only [CollatzResearch.WordTrace]
  refine ⟨4535635937483187736486195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6047514583310916981981593 4535635937483187736486195)
  ·
    refine ⟨6803453906224781604729293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4535635937483187736486195 6803453906224781604729293)
    ·
      refine ⟨2551295214834293101773485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6803453906224781604729293 2551295214834293101773485)
      ·
        refine ⟨956735705562859913165057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2551295214834293101773485 956735705562859913165057)
        ·
          refine ⟨717551779172144934873793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 956735705562859913165057 717551779172144934873793)
          ·
            refine ⟨538163834379108701155345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717551779172144934873793 538163834379108701155345)
            ·
              refine ⟨403622875784331525866509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538163834379108701155345 403622875784331525866509)
              ·
                refine ⟨151358578419124322199941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403622875784331525866509 151358578419124322199941)
                ·
                  refine ⟨28379733453585810412489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151358578419124322199941 28379733453585810412489)
                  ·
                    rfl

theorem cell22_248712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 4].length) (baseStart_248712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248712 prefixEnd_248712 := by exact prefixLift 248712
  have htrace : WordTrace (prefixWord ++ tailWord_248712) baseStart_248712 baseEnd_248712 := by
    simpa [prefixWord, tailWord_248712, baseEnd_248712] using wordTrace_append hprefix tailTrace_248712
  have hstable : (prefixWord ++ tailWord_248712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248712).length < 2 ^ (prefixWord ++ tailWord_248712).sum := by decide
  have hdescent : baseEnd_248712 < baseStart_248712 := by decide
  rcases family_descends (prefixWord ++ tailWord_248712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248714 : List Nat := [3, 1, 2, 4, 1, 3, 2, 1, 1, 4]
def baseStart_248714 : Nat := 118140960795 + 248714 * 2 ^ 59
def prefixEnd_248714 : Nat := 4983230072969 + 3 ^ 40 * 248714 * 2
def baseEnd_248714 : Nat := 85139885001630092687461

theorem tailTrace_248714 : CollatzResearch.WordTrace tailWord_248714 prefixEnd_248714 85139885001630092687461 := by
  unfold tailWord_248714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2267836205239782453636299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6047563213972753209696797 2267836205239782453636299)
  ·
    refine ⟨3401754307859673680454449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2267836205239782453636299 3401754307859673680454449)
    ·
      refine ⟨2551315730894755260340837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3401754307859673680454449 2551315730894755260340837)
      ·
        refine ⟨478371699542766611313907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2551315730894755260340837 478371699542766611313907)
        ·
          refine ⟨717557549314149916970861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478371699542766611313907 717557549314149916970861)
          ·
            refine ⟨269084080992806218864073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 717557549314149916970861 269084080992806218864073)
            ·
              refine ⟨201813060744604664148055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269084080992806218864073 201813060744604664148055)
              ·
                refine ⟨302719591116906996222083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201813060744604664148055 302719591116906996222083)
                ·
                  refine ⟨454079386675360494333125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302719591116906996222083 454079386675360494333125)
                  ·
                    refine ⟨85139885001630092687461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 454079386675360494333125 85139885001630092687461)
                    ·
                      rfl

theorem cell22_248714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_248714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248714 prefixEnd_248714 := by exact prefixLift 248714
  have htrace : WordTrace (prefixWord ++ tailWord_248714) baseStart_248714 baseEnd_248714 := by
    simpa [prefixWord, tailWord_248714, baseEnd_248714] using wordTrace_append hprefix tailTrace_248714
  have hstable : (prefixWord ++ tailWord_248714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248714).length < 2 ^ (prefixWord ++ tailWord_248714).sum := by decide
  have hdescent : baseEnd_248714 < baseStart_248714 := by decide
  rcases family_descends (prefixWord ++ tailWord_248714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248768 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 7]
def baseStart_248768 : Nat := 118140960795 + 248768 * 2 ^ 59
def prefixEnd_248768 : Nat := 4983230072969 + 3 ^ 40 * 248768 * 2
def baseEnd_248768 : Nat := 28386123435063983945765

theorem tailTrace_248768 : CollatzResearch.WordTrace tailWord_248768 prefixEnd_248768 28386123435063983945765 := by
  unfold tailWord_248768
  simp only [CollatzResearch.WordTrace]
  refine ⟨4536657181381748518505479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6048876241842331358007305 4536657181381748518505479)
  ·
    refine ⟨6804985772072622777758219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4536657181381748518505479 6804985772072622777758219)
    ·
      refine ⟨10207478658108934166637329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6804985772072622777758219 10207478658108934166637329)
      ·
        refine ⟨7655608993581700624977997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10207478658108934166637329 7655608993581700624977997)
        ·
          refine ⟨2870853372593137734366749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7655608993581700624977997 2870853372593137734366749)
          ·
            refine ⟨1076570014722426650387531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2870853372593137734366749 1076570014722426650387531)
            ·
              refine ⟨1614855022083639975581297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076570014722426650387531 1614855022083639975581297)
              ·
                refine ⟨1211141266562729981685973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1614855022083639975581297 1211141266562729981685973)
                ·
                  refine ⟨28386123435063983945765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1211141266562729981685973 28386123435063983945765)
                  ·
                    rfl

theorem cell22_248768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_248768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248768 prefixEnd_248768 := by exact prefixLift 248768
  have htrace : WordTrace (prefixWord ++ tailWord_248768) baseStart_248768 baseEnd_248768 := by
    simpa [prefixWord, tailWord_248768, baseEnd_248768] using wordTrace_append hprefix tailTrace_248768
  have hstable : (prefixWord ++ tailWord_248768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248768).length < 2 ^ (prefixWord ++ tailWord_248768).sum := by decide
  have hdescent : baseEnd_248768 < baseStart_248768 := by decide
  rcases family_descends (prefixWord ++ tailWord_248768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248789 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 3, 3]
def baseStart_248789 : Nat := 118140960795 + 248789 * 2 ^ 59
def prefixEnd_248789 : Nat := 4983230072969 + 3 ^ 40 * 248789 * 2
def baseEnd_248789 : Nat := 85165559034354897062231

theorem tailTrace_248789 : CollatzResearch.WordTrace tailWord_248789 prefixEnd_248789 85165559034354897062231 := by
  unfold tailWord_248789
  simp only [CollatzResearch.WordTrace]
  refine ⟨9074080295687417623525421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6049386863791611749016947 9074080295687417623525421)
  ·
    refine ⟨3402780110882781608822033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9074080295687417623525421 3402780110882781608822033)
    ·
      refine ⟨2552085083162086206616525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3402780110882781608822033 2552085083162086206616525)
      ·
        refine ⟨957031906185782327481197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2552085083162086206616525 957031906185782327481197)
        ·
          refine ⟨358886964819668372805449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 957031906185782327481197 358886964819668372805449)
          ·
            refine ⟨269165223614751279604087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358886964819668372805449 269165223614751279604087)
            ·
              refine ⟨403747835422126919406131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269165223614751279604087 403747835422126919406131)
              ·
                refine ⟨605621753133190379109197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403747835422126919406131 605621753133190379109197)
                ·
                  refine ⟨227108157424946392165949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605621753133190379109197 227108157424946392165949)
                  ·
                    refine ⟨85165559034354897062231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227108157424946392165949 85165559034354897062231)
                    ·
                      rfl

theorem cell22_248789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_248789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248789 prefixEnd_248789 := by exact prefixLift 248789
  have htrace : WordTrace (prefixWord ++ tailWord_248789) baseStart_248789 baseEnd_248789 := by
    simpa [prefixWord, tailWord_248789, baseEnd_248789] using wordTrace_append hprefix tailTrace_248789
  have hstable : (prefixWord ++ tailWord_248789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248789).length < 2 ^ (prefixWord ++ tailWord_248789).sum := by decide
  have hdescent : baseEnd_248789 < baseStart_248789 := by decide
  rcases family_descends (prefixWord ++ tailWord_248789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248815 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 3, 4]
def baseStart_248815 : Nat := 118140960795 + 248815 * 2 ^ 59
def prefixEnd_248815 : Nat := 4983230072969 + 3 ^ 40 * 248815 * 2
def baseEnd_248815 : Nat := 85174459365699495912151

theorem tailTrace_248815 : CollatzResearch.WordTrace tailWord_248815 prefixEnd_248815 85174459365699495912151 := by
  unfold tailWord_248815
  simp only [CollatzResearch.WordTrace]
  refine ⟨9075028593593224063971899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6050019062395482709314599 9075028593593224063971899)
  ·
    refine ⟨13612542890389836095957849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9075028593593224063971899 13612542890389836095957849)
    ·
      refine ⟨10209407167792377071968387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13612542890389836095957849 10209407167792377071968387)
      ·
        refine ⟨15314110751688565607952581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10209407167792377071968387 15314110751688565607952581)
        ·
          refine ⟨2871395765941606051491109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15314110751688565607952581 2871395765941606051491109)
          ·
            refine ⟨538386706114051134654583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2871395765941606051491109 538386706114051134654583)
            ·
              refine ⟨807580059171076701981875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538386706114051134654583 807580059171076701981875)
              ·
                refine ⟨1211370088756615052972813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807580059171076701981875 1211370088756615052972813)
                ·
                  refine ⟨454263783283730644864805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1211370088756615052972813 454263783283730644864805)
                  ·
                    refine ⟨85174459365699495912151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 454263783283730644864805 85174459365699495912151)
                    ·
                      rfl

theorem cell22_248815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_248815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248815 prefixEnd_248815 := by exact prefixLift 248815
  have htrace : WordTrace (prefixWord ++ tailWord_248815) baseStart_248815 baseEnd_248815 := by
    simpa [prefixWord, tailWord_248815, baseEnd_248815] using wordTrace_append hprefix tailTrace_248815
  have hstable : (prefixWord ++ tailWord_248815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248815).length < 2 ^ (prefixWord ++ tailWord_248815).sum := by decide
  have hdescent : baseEnd_248815 < baseStart_248815 := by decide
  rcases family_descends (prefixWord ++ tailWord_248815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248875 : List Nat := [1, 1, 1, 1, 2, 1, 9, 6]
def baseStart_248875 : Nat := 118140960795 + 248875 * 2 ^ 59
def prefixEnd_248875 : Nat := 4983230072969 + 3 ^ 40 * 248875 * 2
def baseEnd_248875 : Nat := 9466110954653259934663

theorem tailTrace_248875 : CollatzResearch.WordTrace tailWord_248875 prefixEnd_248875 9466110954653259934663 := by
  unfold tailWord_248875
  simp only [CollatzResearch.WordTrace]
  refine ⟨9077216973375854311156079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6051477982250569540770719 9077216973375854311156079)
  ·
    refine ⟨13615825460063781466734119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9077216973375854311156079 13615825460063781466734119)
    ·
      refine ⟨20423738190095672200101179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13615825460063781466734119 20423738190095672200101179)
      ·
        refine ⟨30635607285143508300151769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20423738190095672200101179 30635607285143508300151769)
        ·
          refine ⟨22976705463857631225113827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30635607285143508300151769 22976705463857631225113827)
          ·
            refine ⟨34465058195786446837670741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22976705463857631225113827 34465058195786446837670741)
            ·
              refine ⟨201943700365936211939477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 34465058195786446837670741 201943700365936211939477)
              ·
                refine ⟨9466110954653259934663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201943700365936211939477 9466110954653259934663)
                ·
                  rfl

theorem cell22_248875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 6].length) (baseStart_248875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248875 prefixEnd_248875 := by exact prefixLift 248875
  have htrace : WordTrace (prefixWord ++ tailWord_248875) baseStart_248875 baseEnd_248875 := by
    simpa [prefixWord, tailWord_248875, baseEnd_248875] using wordTrace_append hprefix tailTrace_248875
  have hstable : (prefixWord ++ tailWord_248875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248875).length < 2 ^ (prefixWord ++ tailWord_248875).sum := by decide
  have hdescent : baseEnd_248875 < baseStart_248875 := by decide
  rcases family_descends (prefixWord ++ tailWord_248875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248926 : List Nat := [4, 4, 1, 1, 1, 1, 4, 6]
def baseStart_248926 : Nat := 118140960795 + 248926 * 2 ^ 59
def prefixEnd_248926 : Nat := 4983230072969 + 3 ^ 40 * 248926 * 2
def baseEnd_248926 : Nat := 9468050770459134042979

theorem tailTrace_248926 : CollatzResearch.WordTrace tailWord_248926 prefixEnd_248926 9468050770459134042979 := by
  unfold tailWord_248926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1134884637023886252657829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6052718064127393347508421 1134884637023886252657829)
  ·
    refine ⟨212790869441978672373343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1134884637023886252657829 212790869441978672373343)
    ·
      refine ⟨319186304162968008560015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212790869441978672373343 319186304162968008560015)
      ·
        refine ⟨478779456244452012840023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319186304162968008560015 478779456244452012840023)
        ·
          refine ⟨718169184366678019260035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478779456244452012840023 718169184366678019260035)
          ·
            refine ⟨1077253776550017028890053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718169184366678019260035 1077253776550017028890053)
            ·
              refine ⟨201985083103128192916885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1077253776550017028890053 201985083103128192916885)
              ·
                refine ⟨9468050770459134042979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201985083103128192916885 9468050770459134042979)
                ·
                  rfl

theorem cell22_248926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_248926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248926 prefixEnd_248926 := by exact prefixLift 248926
  have htrace : WordTrace (prefixWord ++ tailWord_248926) baseStart_248926 baseEnd_248926 := by
    simpa [prefixWord, tailWord_248926, baseEnd_248926] using wordTrace_append hprefix tailTrace_248926
  have hstable : (prefixWord ++ tailWord_248926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248926).length < 2 ^ (prefixWord ++ tailWord_248926).sum := by decide
  have hdescent : baseEnd_248926 < baseStart_248926 := by decide
  rcases family_descends (prefixWord ++ tailWord_248926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248941 : List Nat := [1, 5, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_248941 : Nat := 118140960795 + 248941 * 2 ^ 59
def prefixEnd_248941 : Nat := 4983230072969 + 3 ^ 40 * 248941 * 2
def baseEnd_248941 : Nat := 85217591740677167261765

theorem tailTrace_248941 : CollatzResearch.WordTrace tailWord_248941 prefixEnd_248941 85217591740677167261765 := by
  unfold tailWord_248941
  simp only [CollatzResearch.WordTrace]
  refine ⟨9079624191136747583058677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6053082794091165055372451 9079624191136747583058677)
  ·
    refine ⟨851214767919070085911751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9079624191136747583058677 851214767919070085911751)
    ·
      refine ⟨1276822151878605128867627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 851214767919070085911751 1276822151878605128867627)
      ·
        refine ⟨1915233227817907693301441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1276822151878605128867627 1915233227817907693301441)
        ·
          refine ⟨1436424920863430769976081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1915233227817907693301441 1436424920863430769976081)
          ·
            refine ⟨1077318690647573077482061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1436424920863430769976081 1077318690647573077482061)
            ·
              refine ⟨403994508992839904055773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1077318690647573077482061 403994508992839904055773)
              ·
                refine ⟨151497940872314964020915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403994508992839904055773 151497940872314964020915)
                ·
                  refine ⟨227246911308472446031373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151497940872314964020915 227246911308472446031373)
                  ·
                    refine ⟨85217591740677167261765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227246911308472446031373 85217591740677167261765)
                    ·
                      rfl

theorem cell22_248941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_248941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248941 prefixEnd_248941 := by exact prefixLift 248941
  have htrace : WordTrace (prefixWord ++ tailWord_248941) baseStart_248941 baseEnd_248941 := by
    simpa [prefixWord, tailWord_248941, baseEnd_248941] using wordTrace_append hprefix tailTrace_248941
  have hstable : (prefixWord ++ tailWord_248941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248941).length < 2 ^ (prefixWord ++ tailWord_248941).sum := by decide
  have hdescent : baseEnd_248941 < baseStart_248941 := by decide
  rcases family_descends (prefixWord ++ tailWord_248941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248984 : List Nat := [2, 1, 2, 4, 2, 1, 3, 2, 1, 4]
def baseStart_248984 : Nat := 118140960795 + 248984 * 2 ^ 59
def prefixEnd_248984 : Nat := 4983230072969 + 3 ^ 40 * 248984 * 2
def baseEnd_248984 : Nat := 85232311519439388436633

theorem tailTrace_248984 : CollatzResearch.WordTrace tailWord_248984 prefixEnd_248984 85232311519439388436633 := by
  unfold tailWord_248984
  simp only [CollatzResearch.WordTrace]
  refine ⟨4540596264990482963437003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6054128353320643951249337 4540596264990482963437003)
  ·
    refine ⟨6810894397485724445155505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4540596264990482963437003 6810894397485724445155505)
    ·
      refine ⟨5108170798114293333866629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6810894397485724445155505 5108170798114293333866629)
      ·
        refine ⟨957782024646430000099993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5108170798114293333866629 957782024646430000099993)
        ·
          refine ⟨718336518484822500074995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 957782024646430000099993 718336518484822500074995)
          ·
            refine ⟨1077504777727233750112493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718336518484822500074995 1077504777727233750112493)
            ·
              refine ⟨404064291647712656292185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1077504777727233750112493 404064291647712656292185)
              ·
                refine ⟨303048218735784492219139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404064291647712656292185 303048218735784492219139)
                ·
                  refine ⟨454572328103676738328709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303048218735784492219139 454572328103676738328709)
                  ·
                    refine ⟨85232311519439388436633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 454572328103676738328709 85232311519439388436633)
                    ·
                      rfl

theorem cell22_248984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_248984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248984 prefixEnd_248984 := by exact prefixLift 248984
  have htrace : WordTrace (prefixWord ++ tailWord_248984) baseStart_248984 baseEnd_248984 := by
    simpa [prefixWord, tailWord_248984, baseEnd_248984] using wordTrace_append hprefix tailTrace_248984
  have hstable : (prefixWord ++ tailWord_248984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248984).length < 2 ^ (prefixWord ++ tailWord_248984).sum := by decide
  have hdescent : baseEnd_248984 < baseStart_248984 := by decide
  rcases family_descends (prefixWord ++ tailWord_248984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248995 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 1, 6]
def baseStart_248995 : Nat := 118140960795 + 248995 * 2 ^ 59
def prefixEnd_248995 : Nat := 4983230072969 + 3 ^ 40 * 248995 * 2
def baseEnd_248995 : Nat := 85236077044239026411599

theorem tailTrace_248995 : CollatzResearch.WordTrace tailWord_248995 prefixEnd_248995 85236077044239026411599 := by
  unfold tailWord_248995
  simp only [CollatzResearch.WordTrace]
  refine ⟨9081593732941114805524439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6054395821960743203682959 9081593732941114805524439)
  ·
    refine ⟨13622390599411672208286659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9081593732941114805524439 13622390599411672208286659)
    ·
      refine ⟨20433585899117508312429989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13622390599411672208286659 20433585899117508312429989)
      ·
        refine ⟨3831297356084532808580623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20433585899117508312429989 3831297356084532808580623)
        ·
          refine ⟨5746946034126799212870935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831297356084532808580623 5746946034126799212870935)
          ·
            refine ⟨8620419051190198819306403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746946034126799212870935 8620419051190198819306403)
            ·
              refine ⟨12930628576785298228959605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8620419051190198819306403 12930628576785298228959605)
              ·
                refine ⟨1212246429073621708964963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12930628576785298228959605 1212246429073621708964963)
                ·
                  refine ⟨1818369643610432563447445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1212246429073621708964963 1818369643610432563447445)
                  ·
                    refine ⟨85236077044239026411599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1818369643610432563447445 85236077044239026411599)
                    ·
                      rfl

theorem cell22_248995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 6].length) (baseStart_248995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248995 prefixEnd_248995 := by exact prefixLift 248995
  have htrace : WordTrace (prefixWord ++ tailWord_248995) baseStart_248995 baseEnd_248995 := by
    simpa [prefixWord, tailWord_248995, baseEnd_248995] using wordTrace_append hprefix tailTrace_248995
  have hstable : (prefixWord ++ tailWord_248995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248995).length < 2 ^ (prefixWord ++ tailWord_248995).sum := by decide
  have hdescent : baseEnd_248995 < baseStart_248995 := by decide
  rcases family_descends (prefixWord ++ tailWord_248995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248997 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_248997 : Nat := 118140960795 + 248997 * 2 ^ 59
def prefixEnd_248997 : Nat := 4983230072969 + 3 ^ 40 * 248997 * 2
def baseEnd_248997 : Nat := 85236761685111687861593

theorem tailTrace_248997 : CollatzResearch.WordTrace tailWord_248997 prefixEnd_248997 85236761685111687861593 := by
  unfold tailWord_248997
  simp only [CollatzResearch.WordTrace]
  refine ⟨9081666678933869147097245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6054444452622579431398163 9081666678933869147097245)
  ·
    refine ⟨3405625004600200930161467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9081666678933869147097245 3405625004600200930161467)
    ·
      refine ⟨5108437506900301395242201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3405625004600200930161467 5108437506900301395242201)
      ·
        refine ⟨3831328130175226046431651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5108437506900301395242201 3831328130175226046431651)
        ·
          refine ⟨5746992195262839069647477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831328130175226046431651 5746992195262839069647477)
          ·
            refine ⟨538780518305891162779451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5746992195262839069647477 538780518305891162779451)
            ·
              refine ⟨808170777458836744169177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538780518305891162779451 808170777458836744169177)
              ·
                refine ⟨606128083094127558126883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808170777458836744169177 606128083094127558126883)
                ·
                  refine ⟨909192124641191337190325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606128083094127558126883 909192124641191337190325)
                  ·
                    refine ⟨85236761685111687861593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 909192124641191337190325 85236761685111687861593)
                    ·
                      rfl

theorem cell22_248997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_248997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_248997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_248997 prefixEnd_248997 := by exact prefixLift 248997
  have htrace : WordTrace (prefixWord ++ tailWord_248997) baseStart_248997 baseEnd_248997 := by
    simpa [prefixWord, tailWord_248997, baseEnd_248997] using wordTrace_append hprefix tailTrace_248997
  have hstable : (prefixWord ++ tailWord_248997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248997).length < 2 ^ (prefixWord ++ tailWord_248997).sum := by decide
  have hdescent : baseEnd_248997 < baseStart_248997 := by decide
  rcases family_descends (prefixWord ++ tailWord_248997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249010 : List Nat := [3, 2, 1, 1, 1, 14]
def baseStart_249010 : Nat := 118140960795 + 249010 * 2 ^ 59
def prefixEnd_249010 : Nat := 4983230072969 + 3 ^ 40 * 249010 * 2
def baseEnd_249010 : Nat := 1052360640133135645513

theorem tailTrace_249010 : CollatzResearch.WordTrace tailWord_249010 prefixEnd_249010 1052360640133135645513 := by
  unfold tailWord_249010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2270535206971693091830121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6054760551924514911546989 2270535206971693091830121)
  ·
    refine ⟨1702901405228769818872591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2270535206971693091830121 1702901405228769818872591)
    ·
      refine ⟨2554352107843154728308887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702901405228769818872591 2554352107843154728308887)
      ·
        refine ⟨3831528161764732092463331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2554352107843154728308887 3831528161764732092463331)
        ·
          refine ⟨5747292242647098138694997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831528161764732092463331 5747292242647098138694997)
          ·
            refine ⟨1052360640133135645513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 5747292242647098138694997 1052360640133135645513)
            ·
              rfl

theorem cell22_249010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 14].length) (baseStart_249010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249010 prefixEnd_249010 := by exact prefixLift 249010
  have htrace : WordTrace (prefixWord ++ tailWord_249010) baseStart_249010 baseEnd_249010 := by
    simpa [prefixWord, tailWord_249010, baseEnd_249010] using wordTrace_append hprefix tailTrace_249010
  have hstable : (prefixWord ++ tailWord_249010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249010).length < 2 ^ (prefixWord ++ tailWord_249010).sum := by decide
  have hdescent : baseEnd_249010 < baseStart_249010 := by decide
  rcases family_descends (prefixWord ++ tailWord_249010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249046 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_249046 : Nat := 118140960795 + 249046 * 2 ^ 59
def prefixEnd_249046 : Nat := 4983230072969 + 3 ^ 40 * 249046 * 2
def baseEnd_249046 : Nat := 85253535386491893386443

theorem tailTrace_249046 : CollatzResearch.WordTrace tailWord_249046 prefixEnd_249046 85253535386491893386443 := by
  unfold tailWord_249046
  simp only [CollatzResearch.WordTrace]
  refine ⟨567715865984771907226937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6055635903837567010420661 567715865984771907226937)
  ·
    refine ⟨425786899488578930420203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 567715865984771907226937 425786899488578930420203)
    ·
      refine ⟨638680349232868395630305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425786899488578930420203 638680349232868395630305)
      ·
        refine ⟨479010261924651296722729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638680349232868395630305 479010261924651296722729)
        ·
          refine ⟨359257696443488472542047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479010261924651296722729 359257696443488472542047)
          ·
            refine ⟨538886544665232708813071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359257696443488472542047 538886544665232708813071)
            ·
              refine ⟨808329816997849063219607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538886544665232708813071 808329816997849063219607)
              ·
                refine ⟨1212494725496773594829411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808329816997849063219607 1212494725496773594829411)
                ·
                  refine ⟨1818742088245160392244117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1212494725496773594829411 1818742088245160392244117)
                  ·
                    refine ⟨85253535386491893386443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1818742088245160392244117 85253535386491893386443)
                    ·
                      rfl

theorem cell22_249046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_249046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249046 prefixEnd_249046 := by exact prefixLift 249046
  have htrace : WordTrace (prefixWord ++ tailWord_249046) baseStart_249046 baseEnd_249046 := by
    simpa [prefixWord, tailWord_249046, baseEnd_249046] using wordTrace_append hprefix tailTrace_249046
  have hstable : (prefixWord ++ tailWord_249046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249046).length < 2 ^ (prefixWord ++ tailWord_249046).sum := by decide
  have hdescent : baseEnd_249046 < baseStart_249046 := by decide
  rcases family_descends (prefixWord ++ tailWord_249046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249087 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 2, 5]
def baseStart_249087 : Nat := 118140960795 + 249087 * 2 ^ 59
def prefixEnd_249087 : Nat := 4983230072969 + 3 ^ 40 * 249087 * 2
def baseEnd_249087 : Nat := 85267570524381453111317

theorem tailTrace_249087 : CollatzResearch.WordTrace tailWord_249087 prefixEnd_249087 85267570524381453111317 := by
  unfold tailWord_249087
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084949248607814517873515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6056632832405209678582343 9084949248607814517873515)
  ·
    refine ⟨13627423872911721776810273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9084949248607814517873515 13627423872911721776810273)
    ·
      refine ⟨10220567904683791332607705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13627423872911721776810273 10220567904683791332607705)
      ·
        refine ⟨7665425928512843499455779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10220567904683791332607705 7665425928512843499455779)
        ·
          refine ⟨11498138892769265249183669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7665425928512843499455779 11498138892769265249183669)
          ·
            refine ⟨1077950521197118617110969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11498138892769265249183669 1077950521197118617110969)
            ·
              refine ⟨808462890897838962833227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077950521197118617110969 808462890897838962833227)
              ·
                refine ⟨1212694336346758444249841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808462890897838962833227 1212694336346758444249841)
                ·
                  refine ⟨909520752260068833187381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1212694336346758444249841 909520752260068833187381)
                  ·
                    refine ⟨85267570524381453111317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 909520752260068833187381 85267570524381453111317)
                    ·
                      rfl

theorem cell22_249087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_249087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249087 prefixEnd_249087 := by exact prefixLift 249087
  have htrace : WordTrace (prefixWord ++ tailWord_249087) baseStart_249087 baseEnd_249087 := by
    simpa [prefixWord, tailWord_249087, baseEnd_249087] using wordTrace_append hprefix tailTrace_249087
  have hstable : (prefixWord ++ tailWord_249087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249087).length < 2 ^ (prefixWord ++ tailWord_249087).sum := by decide
  have hdescent : baseEnd_249087 < baseStart_249087 := by decide
  rcases family_descends (prefixWord ++ tailWord_249087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249153 : List Nat := [1, 2, 5, 2, 1, 3, 1, 2, 1, 4]
def baseStart_249153 : Nat := 118140960795 + 249153 * 2 ^ 59
def prefixEnd_249153 : Nat := 4983230072969 + 3 ^ 40 * 249153 * 2
def baseEnd_249153 : Nat := 85290163673179280961115

theorem tailTrace_249153 : CollatzResearch.WordTrace tailWord_249153 prefixEnd_249153 85290163673179280961115 := by
  unfold tailWord_249153
  simp only [CollatzResearch.WordTrace]
  refine ⟨9087356466368707789776113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6058237644245805193184075 9087356466368707789776113)
  ·
    refine ⟨6815517349776530842332085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9087356466368707789776113 6815517349776530842332085)
    ·
      refine ⟨638954751541549766468633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6815517349776530842332085 638954751541549766468633)
      ·
        refine ⟨479216063656162324851475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638954751541549766468633 479216063656162324851475)
        ·
          refine ⟨718824095484243487277213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479216063656162324851475 718824095484243487277213)
          ·
            refine ⟨269559035806591307728955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 718824095484243487277213 269559035806591307728955)
            ·
              refine ⟨404338553709886961593433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269559035806591307728955 404338553709886961593433)
              ·
                refine ⟨303253915282415221195075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404338553709886961593433 303253915282415221195075)
                ·
                  refine ⟨454880872923622831792613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303253915282415221195075 454880872923622831792613)
                  ·
                    refine ⟨85290163673179280961115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 454880872923622831792613 85290163673179280961115)
                    ·
                      rfl

theorem cell22_249153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_249153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249153 prefixEnd_249153 := by exact prefixLift 249153
  have htrace : WordTrace (prefixWord ++ tailWord_249153) baseStart_249153 baseEnd_249153 := by
    simpa [prefixWord, tailWord_249153, baseEnd_249153] using wordTrace_append hprefix tailTrace_249153
  have hstable : (prefixWord ++ tailWord_249153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249153).length < 2 ^ (prefixWord ++ tailWord_249153).sum := by decide
  have hdescent : baseEnd_249153 < baseStart_249153 := by decide
  rcases family_descends (prefixWord ++ tailWord_249153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249164 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_249164 : Nat := 118140960795 + 249164 * 2 ^ 59
def prefixEnd_249164 : Nat := 4983230072969 + 3 ^ 40 * 249164 * 2
def baseEnd_249164 : Nat := 85293929197978918936081

theorem tailTrace_249164 : CollatzResearch.WordTrace tailWord_249164 prefixEnd_249164 85293929197978918936081 := by
  unfold tailWord_249164
  simp only [CollatzResearch.WordTrace]
  refine ⟨4543878834664428334213273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6058505112885904445617697 4543878834664428334213273)
  ·
    refine ⟨3407909125998321250659955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4543878834664428334213273 3407909125998321250659955)
    ·
      refine ⟨5111863688997481875989933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3407909125998321250659955 5111863688997481875989933)
      ·
        refine ⟨1916948883374055703496225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5111863688997481875989933 1916948883374055703496225)
        ·
          refine ⟨1437711662530541777622169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1916948883374055703496225 1437711662530541777622169)
          ·
            refine ⟨1078283746897906333216627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1437711662530541777622169 1078283746897906333216627)
            ·
              refine ⟨1617425620346859499824941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078283746897906333216627 1617425620346859499824941)
              ·
                refine ⟨606534607630072312434353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1617425620346859499824941 606534607630072312434353)
                ·
                  refine ⟨454900955722554234325765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606534607630072312434353 454900955722554234325765)
                  ·
                    refine ⟨85293929197978918936081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 454900955722554234325765 85293929197978918936081)
                    ·
                      rfl

theorem cell22_249164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_249164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249164 prefixEnd_249164 := by exact prefixLift 249164
  have htrace : WordTrace (prefixWord ++ tailWord_249164) baseStart_249164 baseEnd_249164 := by
    simpa [prefixWord, tailWord_249164, baseEnd_249164] using wordTrace_append hprefix tailTrace_249164
  have hstable : (prefixWord ++ tailWord_249164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249164).length < 2 ^ (prefixWord ++ tailWord_249164).sum := by decide
  have hdescent : baseEnd_249164 < baseStart_249164 := by decide
  rcases family_descends (prefixWord ++ tailWord_249164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249228 : List Nat := [2, 2, 1, 2, 1, 3, 4, 3, 1, 3]
def baseStart_249228 : Nat := 118140960795 + 249228 * 2 ^ 59
def prefixEnd_249228 : Nat := 4983230072969 + 3 ^ 40 * 249228 * 2
def baseEnd_249228 : Nat := 85315837705904085335885

theorem tailTrace_249228 : CollatzResearch.WordTrace tailWord_249228 prefixEnd_249228 85315837705904085335885 := by
  unfold tailWord_249228
  simp only [CollatzResearch.WordTrace]
  refine ⟨4545045970548497799378169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6060061294064663732504225 4545045970548497799378169)
  ·
    refine ⟨3408784477911373349533627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4545045970548497799378169 3408784477911373349533627)
    ·
      refine ⟨5113176716867060024300441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3408784477911373349533627 5113176716867060024300441)
      ·
        refine ⟨3834882537650295018225331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5113176716867060024300441 3834882537650295018225331)
        ·
          refine ⟨5752323806475442527337997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3834882537650295018225331 5752323806475442527337997)
          ·
            refine ⟨2157121427428290947751749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5752323806475442527337997 2157121427428290947751749)
            ·
              refine ⟨404460267642804552703453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2157121427428290947751749 404460267642804552703453)
              ·
                refine ⟨151672600366051707263795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404460267642804552703453 151672600366051707263795)
                ·
                  refine ⟨227508900549077560895693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151672600366051707263795 227508900549077560895693)
                  ·
                    refine ⟨85315837705904085335885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227508900549077560895693 85315837705904085335885)
                    ·
                      rfl

theorem cell22_249228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_249228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249228 prefixEnd_249228 := by exact prefixLift 249228
  have htrace : WordTrace (prefixWord ++ tailWord_249228) baseStart_249228 baseEnd_249228 := by
    simpa [prefixWord, tailWord_249228, baseEnd_249228] using wordTrace_append hprefix tailTrace_249228
  have hstable : (prefixWord ++ tailWord_249228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249228).length < 2 ^ (prefixWord ++ tailWord_249228).sum := by decide
  have hdescent : baseEnd_249228 < baseStart_249228 := by decide
  rcases family_descends (prefixWord ++ tailWord_249228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249241 : List Nat := [1, 2, 1, 2, 1, 7, 1, 2, 5]
def baseStart_249241 : Nat := 118140960795 + 249241 * 2 ^ 59
def prefixEnd_249241 : Nat := 4983230072969 + 3 ^ 40 * 249241 * 2
def baseEnd_249241 : Nat := 28440095957192128253615

theorem tailTrace_249241 : CollatzResearch.WordTrace tailWord_249241 prefixEnd_249241 28440095957192128253615 := by
  unfold tailWord_249241
  simp only [CollatzResearch.WordTrace]
  refine ⟨9090566090049898818979577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6060377393366599212653051 9090566090049898818979577)
  ·
    refine ⟨6817924567537424114234683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9090566090049898818979577 6817924567537424114234683)
    ·
      refine ⟨10226886851306136171352025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6817924567537424114234683 10226886851306136171352025)
      ·
        refine ⟨7670165138479602128514019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10226886851306136171352025 7670165138479602128514019)
        ·
          refine ⟨11505247707719403192771029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7670165138479602128514019 11505247707719403192771029)
          ·
            refine ⟨269654243149673512330571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 11505247707719403192771029 269654243149673512330571)
            ·
              refine ⟨404481364724510268495857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269654243149673512330571 404481364724510268495857)
              ·
                refine ⟨303361023543382701371893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404481364724510268495857 303361023543382701371893)
                ·
                  refine ⟨28440095957192128253615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 303361023543382701371893 28440095957192128253615)
                  ·
                    rfl

theorem cell22_249241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 5].length) (baseStart_249241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249241 prefixEnd_249241 := by exact prefixLift 249241
  have htrace : WordTrace (prefixWord ++ tailWord_249241) baseStart_249241 baseEnd_249241 := by
    simpa [prefixWord, tailWord_249241, baseEnd_249241] using wordTrace_append hprefix tailTrace_249241
  have hstable : (prefixWord ++ tailWord_249241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249241).length < 2 ^ (prefixWord ++ tailWord_249241).sum := by decide
  have hdescent : baseEnd_249241 < baseStart_249241 := by decide
  rcases family_descends (prefixWord ++ tailWord_249241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249271 : List Nat := [1, 1, 3, 1, 3, 2, 4, 2, 1, 4]
def baseStart_249271 : Nat := 118140960795 + 249271 * 2 ^ 59
def prefixEnd_249271 : Nat := 4983230072969 + 3 ^ 40 * 249271 * 2
def baseEnd_249271 : Nat := 85330557484666306510753

theorem tailTrace_249271 : CollatzResearch.WordTrace tailWord_249271 prefixEnd_249271 85330557484666306510753 := by
  unfold tailWord_249271
  simp only [CollatzResearch.WordTrace]
  refine ⟨9091660279941213942571667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6061106853294142628381111 9091660279941213942571667)
  ·
    refine ⟨13637490419911820913857501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9091660279941213942571667 13637490419911820913857501)
    ·
      refine ⟨5114058907466932842696563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13637490419911820913857501 5114058907466932842696563)
      ·
        refine ⟨7671088361200399264044845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5114058907466932842696563 7671088361200399264044845)
        ·
          refine ⟨2876658135450149724016817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7671088361200399264044845 2876658135450149724016817)
          ·
            refine ⟨2157493601587612293012613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2876658135450149724016817 2157493601587612293012613)
            ·
              refine ⟨404530050297677304939865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2157493601587612293012613 404530050297677304939865)
              ·
                refine ⟨303397537723257978704899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404530050297677304939865 303397537723257978704899)
                ·
                  refine ⟨455096306584886968057349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303397537723257978704899 455096306584886968057349)
                  ·
                    refine ⟨85330557484666306510753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 455096306584886968057349 85330557484666306510753)
                    ·
                      rfl

theorem cell22_249271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_249271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249271 prefixEnd_249271 := by exact prefixLift 249271
  have htrace : WordTrace (prefixWord ++ tailWord_249271) baseStart_249271 baseEnd_249271 := by
    simpa [prefixWord, tailWord_249271, baseEnd_249271] using wordTrace_append hprefix tailTrace_249271
  have hstable : (prefixWord ++ tailWord_249271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249271).length < 2 ^ (prefixWord ++ tailWord_249271).sum := by decide
  have hdescent : baseEnd_249271 < baseStart_249271 := by decide
  rcases family_descends (prefixWord ++ tailWord_249271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249301 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 4, 3]
def baseStart_249301 : Nat := 118140960795 + 249301 * 2 ^ 59
def prefixEnd_249301 : Nat := 4983230072969 + 3 ^ 40 * 249301 * 2
def baseEnd_249301 : Nat := 85340827097756228260661

theorem tailTrace_249301 : CollatzResearch.WordTrace tailWord_249301 prefixEnd_249301 85340827097756228260661 := by
  unfold tailWord_249301
  simp only [CollatzResearch.WordTrace]
  refine ⟨9092754469832529066163757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6061836313221686044109171 9092754469832529066163757)
  ·
    refine ⟨3409782926187198399811409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9092754469832529066163757 3409782926187198399811409)
    ·
      refine ⟨2557337194640398799858557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3409782926187198399811409 2557337194640398799858557)
      ·
        refine ⟨959001447990149549946959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2557337194640398799858557 959001447990149549946959)
        ·
          refine ⟨1438502171985224324920439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959001447990149549946959 1438502171985224324920439)
          ·
            refine ⟨2157753257977836487380659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438502171985224324920439 2157753257977836487380659)
            ·
              refine ⟨3236629886966754731070989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157753257977836487380659 3236629886966754731070989)
              ·
                refine ⟨1213736207612533024151621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3236629886966754731070989 1213736207612533024151621)
                ·
                  refine ⟨227575538927349942028429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1213736207612533024151621 227575538927349942028429)
                  ·
                    refine ⟨85340827097756228260661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227575538927349942028429 85340827097756228260661)
                    ·
                      rfl

theorem cell22_249301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_249301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249301 prefixEnd_249301 := by exact prefixLift 249301
  have htrace : WordTrace (prefixWord ++ tailWord_249301) baseStart_249301 baseEnd_249301 := by
    simpa [prefixWord, tailWord_249301, baseEnd_249301] using wordTrace_append hprefix tailTrace_249301
  have hstable : (prefixWord ++ tailWord_249301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249301).length < 2 ^ (prefixWord ++ tailWord_249301).sum := by decide
  have hdescent : baseEnd_249301 < baseStart_249301 := by decide
  rcases family_descends (prefixWord ++ tailWord_249301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249333 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_249333 : Nat := 118140960795 + 249333 * 2 ^ 59
def prefixEnd_249333 : Nat := 4983230072969 + 3 ^ 40 * 249333 * 2
def baseEnd_249333 : Nat := 85351781351718811460563

theorem tailTrace_249333 : CollatzResearch.WordTrace tailWord_249333 prefixEnd_249333 85351781351718811460563 := by
  unfold tailWord_249333
  simp only [CollatzResearch.WordTrace]
  refine ⟨9093921605716598531328653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6062614403811065687552435 9093921605716598531328653)
  ·
    refine ⟨3410220602143724449248245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9093921605716598531328653 3410220602143724449248245)
    ·
      refine ⟨319708181450974167117023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3410220602143724449248245 319708181450974167117023)
      ·
        refine ⟨479562272176461250675535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319708181450974167117023 479562272176461250675535)
        ·
          refine ⟨719343408264691876013303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479562272176461250675535 719343408264691876013303)
          ·
            refine ⟨1079015112397037814019955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719343408264691876013303 1079015112397037814019955)
            ·
              refine ⟨1618522668595556721029933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079015112397037814019955 1618522668595556721029933)
              ·
                refine ⟨606946000723333770386225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1618522668595556721029933 606946000723333770386225)
                ·
                  refine ⟨455209500542500327789669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606946000723333770386225 455209500542500327789669)
                  ·
                    refine ⟨85351781351718811460563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 455209500542500327789669 85351781351718811460563)
                    ·
                      rfl

theorem cell22_249333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_249333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249333 prefixEnd_249333 := by exact prefixLift 249333
  have htrace : WordTrace (prefixWord ++ tailWord_249333) baseStart_249333 baseEnd_249333 := by
    simpa [prefixWord, tailWord_249333, baseEnd_249333] using wordTrace_append hprefix tailTrace_249333
  have hstable : (prefixWord ++ tailWord_249333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249333).length < 2 ^ (prefixWord ++ tailWord_249333).sum := by decide
  have hdescent : baseEnd_249333 < baseStart_249333 := by decide
  rcases family_descends (prefixWord ++ tailWord_249333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249532 : List Nat := [2, 2, 2, 3, 1, 3, 1, 4, 1, 3]
def baseStart_249532 : Nat := 118140960795 + 249532 * 2 ^ 59
def prefixEnd_249532 : Nat := 4983230072969 + 3 ^ 40 * 249532 * 2
def baseEnd_249532 : Nat := 85419903118548625734953

theorem tailTrace_249532 : CollatzResearch.WordTrace tailWord_249532 prefixEnd_249532 85419903118548625734953 := by
  unfold tailWord_249532
  simp only [CollatzResearch.WordTrace]
  refine ⟨4550589865997827758911425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6067453154663770345215233 4550589865997827758911425)
  ·
    refine ⟨3412942399498370819183569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4550589865997827758911425 3412942399498370819183569)
    ·
      refine ⟨2559706799623778114387677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3412942399498370819183569 2559706799623778114387677)
      ·
        refine ⟨959890049858916792895379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2559706799623778114387677 959890049858916792895379)
        ·
          refine ⟨1439835074788375189343069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959890049858916792895379 1439835074788375189343069)
          ·
            refine ⟨539938153045640696003651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1439835074788375189343069 539938153045640696003651)
            ·
              refine ⟨809907229568461044005477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539938153045640696003651 809907229568461044005477)
              ·
                refine ⟨151857605544086445751027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 809907229568461044005477 151857605544086445751027)
                ·
                  refine ⟨227786408316129668626541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151857605544086445751027 227786408316129668626541)
                  ·
                    refine ⟨85419903118548625734953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227786408316129668626541 85419903118548625734953)
                    ·
                      rfl

theorem cell22_249532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_249532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249532 prefixEnd_249532 := by exact prefixLift 249532
  have htrace : WordTrace (prefixWord ++ tailWord_249532) baseStart_249532 baseEnd_249532 := by
    simpa [prefixWord, tailWord_249532, baseEnd_249532] using wordTrace_append hprefix tailTrace_249532
  have hstable : (prefixWord ++ tailWord_249532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249532).length < 2 ^ (prefixWord ++ tailWord_249532).sum := by decide
  have hdescent : baseEnd_249532 < baseStart_249532 := by decide
  rcases family_descends (prefixWord ++ tailWord_249532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249590 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_249590 : Nat := 118140960795 + 249590 * 2 ^ 59
def prefixEnd_249590 : Nat := 4983230072969 + 3 ^ 40 * 249590 * 2
def baseEnd_249590 : Nat := 28479919234618602594925

theorem tailTrace_249590 : CollatzResearch.WordTrace tailWord_249590 prefixEnd_249590 28479919234618602594925 := by
  unfold tailWord_249590
  simp only [CollatzResearch.WordTrace]
  refine ⟨568955947861595713964639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6068863443857020948956149 568955947861595713964639)
  ·
    refine ⟨853433921792393570946959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 568955947861595713964639 853433921792393570946959)
    ·
      refine ⟨1280150882688590356420439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 853433921792393570946959 1280150882688590356420439)
      ·
        refine ⟨1920226324032885534630659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1280150882688590356420439 1920226324032885534630659)
        ·
          refine ⟨2880339486049328301945989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1920226324032885534630659 2880339486049328301945989)
          ·
            refine ⟨540063653634249056614873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2880339486049328301945989 540063653634249056614873)
            ·
              refine ⟨405047740225686792461155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540063653634249056614873 405047740225686792461155)
              ·
                refine ⟨607571610338530188691733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405047740225686792461155 607571610338530188691733)
                ·
                  refine ⟨28479919234618602594925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 607571610338530188691733 28479919234618602594925)
                  ·
                    rfl

theorem cell22_249590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_249590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249590 prefixEnd_249590 := by exact prefixLift 249590
  have htrace : WordTrace (prefixWord ++ tailWord_249590) baseStart_249590 baseEnd_249590 := by
    simpa [prefixWord, tailWord_249590, baseEnd_249590] using wordTrace_append hprefix tailTrace_249590
  have hstable : (prefixWord ++ tailWord_249590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249590).length < 2 ^ (prefixWord ++ tailWord_249590).sum := by decide
  have hdescent : baseEnd_249590 < baseStart_249590 := by decide
  rcases family_descends (prefixWord ++ tailWord_249590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249678 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_249678 : Nat := 118140960795 + 249678 * 2 ^ 59
def prefixEnd_249678 : Nat := 4983230072969 + 3 ^ 40 * 249678 * 2
def baseEnd_249678 : Nat := 85469881902252911584505

theorem tailTrace_249678 : CollatzResearch.WordTrace tailWord_249678 prefixEnd_249678 85469881902252911584505 := by
  unfold tailWord_249678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1138313098683340306579711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6071003192977814968425125 1138313098683340306579711)
  ·
    refine ⟨1707469648025010459869567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1138313098683340306579711 1707469648025010459869567)
    ·
      refine ⟨2561204472037515689804351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1707469648025010459869567 2561204472037515689804351)
      ·
        refine ⟨3841806708056273534706527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561204472037515689804351 3841806708056273534706527)
        ·
          refine ⟨5762710062084410302059791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841806708056273534706527 5762710062084410302059791)
          ·
            refine ⟨8644065093126615453089687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5762710062084410302059791 8644065093126615453089687)
            ·
              refine ⟨12966097639689923179634531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8644065093126615453089687 12966097639689923179634531)
              ·
                refine ⟨19449146459534884769451797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12966097639689923179634531 19449146459534884769451797)
                ·
                  refine ⟨911678740290697723568053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19449146459534884769451797 911678740290697723568053)
                  ·
                    refine ⟨85469881902252911584505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 911678740290697723568053 85469881902252911584505)
                    ·
                      rfl

theorem cell22_249678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_249678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249678 prefixEnd_249678 := by exact prefixLift 249678
  have htrace : WordTrace (prefixWord ++ tailWord_249678) baseStart_249678 baseEnd_249678 := by
    simpa [prefixWord, tailWord_249678, baseEnd_249678] using wordTrace_append hprefix tailTrace_249678
  have hstable : (prefixWord ++ tailWord_249678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249678).length < 2 ^ (prefixWord ++ tailWord_249678).sum := by decide
  have hdescent : baseEnd_249678 < baseStart_249678 := by decide
  rcases family_descends (prefixWord ++ tailWord_249678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249740 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 4, 3]
def baseStart_249740 : Nat := 118140960795 + 249740 * 2 ^ 59
def prefixEnd_249740 : Nat := 4983230072969 + 3 ^ 40 * 249740 * 2
def baseEnd_249740 : Nat := 85491105769305416534315

theorem tailTrace_249740 : CollatzResearch.WordTrace tailWord_249740 prefixEnd_249740 85491105769305416534315 := by
  unfold tailWord_249740
  simp only [CollatzResearch.WordTrace]
  refine ⟨4554383057621053520697337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6072510743494738027596449 4554383057621053520697337)
  ·
    refine ⟨3415787293215790140523003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4554383057621053520697337 3415787293215790140523003)
    ·
      refine ⟨5123680939823685210784505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3415787293215790140523003 5123680939823685210784505)
      ·
        refine ⟨3842760704867763908088379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5123680939823685210784505 3842760704867763908088379)
        ·
          refine ⟨5764141057301645862132569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3842760704867763908088379 5764141057301645862132569)
          ·
            refine ⟨4323105792976234396599427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5764141057301645862132569 4323105792976234396599427)
            ·
              refine ⟨6484658689464351594899141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323105792976234396599427 6484658689464351594899141)
              ·
                refine ⟨1215873504274565924043589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6484658689464351594899141 1215873504274565924043589)
                ·
                  refine ⟨227976282051481110758173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1215873504274565924043589 227976282051481110758173)
                  ·
                    refine ⟨85491105769305416534315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227976282051481110758173 85491105769305416534315)
                    ·
                      rfl

theorem cell22_249740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_249740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249740 prefixEnd_249740 := by exact prefixLift 249740
  have htrace : WordTrace (prefixWord ++ tailWord_249740) baseStart_249740 baseEnd_249740 := by
    simpa [prefixWord, tailWord_249740, baseEnd_249740] using wordTrace_append hprefix tailTrace_249740
  have hstable : (prefixWord ++ tailWord_249740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249740).length < 2 ^ (prefixWord ++ tailWord_249740).sum := by decide
  have hdescent : baseEnd_249740 < baseStart_249740 := by decide
  rcases family_descends (prefixWord ++ tailWord_249740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249757 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_249757 : Nat := 118140960795 + 249757 * 2 ^ 59
def prefixEnd_249757 : Nat := 4983230072969 + 3 ^ 40 * 249757 * 2
def baseEnd_249757 : Nat := 85496925216723038859263

theorem tailTrace_249757 : CollatzResearch.WordTrace tailWord_249757 prefixEnd_249757 85496925216723038859263 := by
  unfold tailWord_249757
  simp only [CollatzResearch.WordTrace]
  refine ⟨9109386156180518944763525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6072924104120345963175683 9109386156180518944763525)
  ·
    refine ⟨1708009904283847302143161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9109386156180518944763525 1708009904283847302143161)
    ·
      refine ⟨1281007428212885476607371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1708009904283847302143161 1281007428212885476607371)
      ·
        refine ⟨1921511142319328214911057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281007428212885476607371 1921511142319328214911057)
        ·
          refine ⟨1441133356739496161183293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1921511142319328214911057 1441133356739496161183293)
          ·
            refine ⟨540425008777311060443735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1441133356739496161183293 540425008777311060443735)
            ·
              refine ⟨810637513165966590665603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540425008777311060443735 810637513165966590665603)
              ·
                refine ⟨1215956269748949885998405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810637513165966590665603 1215956269748949885998405)
                ·
                  refine ⟨227991800577928103624701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1215956269748949885998405 227991800577928103624701)
                  ·
                    refine ⟨85496925216723038859263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227991800577928103624701 85496925216723038859263)
                    ·
                      rfl

theorem cell22_249757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_249757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249757 prefixEnd_249757 := by exact prefixLift 249757
  have htrace : WordTrace (prefixWord ++ tailWord_249757) baseStart_249757 baseEnd_249757 := by
    simpa [prefixWord, tailWord_249757, baseEnd_249757] using wordTrace_append hprefix tailTrace_249757
  have hstable : (prefixWord ++ tailWord_249757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249757).length < 2 ^ (prefixWord ++ tailWord_249757).sum := by decide
  have hdescent : baseEnd_249757 < baseStart_249757 := by decide
  rcases family_descends (prefixWord ++ tailWord_249757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249815 : List Nat := [1, 1, 3, 2, 1, 1, 4, 4, 5]
def baseStart_249815 : Nat := 118140960795 + 249815 * 2 ^ 59
def prefixEnd_249815 : Nat := 4983230072969 + 3 ^ 40 * 249815 * 2
def baseEnd_249815 : Nat := 28505593267343406969695

theorem tailTrace_249815 : CollatzResearch.WordTrace tailWord_249815 prefixEnd_249815 28505593267343406969695 := by
  unfold tailWord_249815
  simp only [CollatzResearch.WordTrace]
  refine ⟨9111501589970394850374899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6074334393313596566916599 9111501589970394850374899)
  ·
    refine ⟨13667252384955592275562349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9111501589970394850374899 13667252384955592275562349)
    ·
      refine ⟨5125219644358347103335881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13667252384955592275562349 5125219644358347103335881)
      ·
        refine ⟨3843914733268760327501911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5125219644358347103335881 3843914733268760327501911)
        ·
          refine ⟨5765872099903140491252867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3843914733268760327501911 5765872099903140491252867)
          ·
            refine ⟨8648808149854710736879301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5765872099903140491252867 8648808149854710736879301)
            ·
              refine ⟨1621651528097758263164869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8648808149854710736879301 1621651528097758263164869)
              ·
                refine ⟨304059661518329674343413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1621651528097758263164869 304059661518329674343413)
                ·
                  refine ⟨28505593267343406969695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 304059661518329674343413 28505593267343406969695)
                  ·
                    rfl

theorem cell22_249815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 5].length) (baseStart_249815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249815 prefixEnd_249815 := by exact prefixLift 249815
  have htrace : WordTrace (prefixWord ++ tailWord_249815) baseStart_249815 baseEnd_249815 := by
    simpa [prefixWord, tailWord_249815, baseEnd_249815] using wordTrace_append hprefix tailTrace_249815
  have hstable : (prefixWord ++ tailWord_249815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249815).length < 2 ^ (prefixWord ++ tailWord_249815).sum := by decide
  have hdescent : baseEnd_249815 < baseStart_249815 := by decide
  rcases family_descends (prefixWord ++ tailWord_249815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249907 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 2, 4]
def baseStart_249907 : Nat := 118140960795 + 249907 * 2 ^ 59
def prefixEnd_249907 : Nat := 4983230072969 + 3 ^ 40 * 249907 * 2
def baseEnd_249907 : Nat := 85548273282172647608803

theorem tailTrace_249907 : CollatzResearch.WordTrace tailWord_249907 prefixEnd_249907 85548273282172647608803 := by
  unfold tailWord_249907
  simp only [CollatzResearch.WordTrace]
  refine ⟨9114857105637094562723975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6076571403758063041815983 9114857105637094562723975)
  ·
    refine ⟨13672285658455641844085963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9114857105637094562723975 13672285658455641844085963)
    ·
      refine ⟨20508428487683462766128945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13672285658455641844085963 20508428487683462766128945)
      ·
        refine ⟨15381321365762597074596709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20508428487683462766128945 15381321365762597074596709)
        ·
          refine ⟨2883997756080486951486883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15381321365762597074596709 2883997756080486951486883)
          ·
            refine ⟨4325996634120730427230325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883997756080486951486883 4325996634120730427230325)
            ·
              refine ⟨405562184448818477552843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4325996634120730427230325 405562184448818477552843)
              ·
                refine ⟨608343276673227716329265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405562184448818477552843 608343276673227716329265)
                ·
                  refine ⟨456257457504920787246949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608343276673227716329265 456257457504920787246949)
                  ·
                    refine ⟨85548273282172647608803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 456257457504920787246949 85548273282172647608803)
                    ·
                      rfl

theorem cell22_249907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 4].length) (baseStart_249907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249907 prefixEnd_249907 := by exact prefixLift 249907
  have htrace : WordTrace (prefixWord ++ tailWord_249907) baseStart_249907 baseEnd_249907 := by
    simpa [prefixWord, tailWord_249907, baseEnd_249907] using wordTrace_append hprefix tailTrace_249907
  have hstable : (prefixWord ++ tailWord_249907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249907).length < 2 ^ (prefixWord ++ tailWord_249907).sum := by decide
  have hdescent : baseEnd_249907 < baseStart_249907 := by decide
  rcases family_descends (prefixWord ++ tailWord_249907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249913 : List Nat := [1, 2, 1, 5, 4, 1, 2, 1, 1, 4]
def baseStart_249913 : Nat := 118140960795 + 249913 * 2 ^ 59
def prefixEnd_249913 : Nat := 4983230072969 + 3 ^ 40 * 249913 * 2
def baseEnd_249913 : Nat := 85550327204790631958785

theorem tailTrace_249913 : CollatzResearch.WordTrace tailWord_249913 prefixEnd_249913 85550327204790631958785 := by
  unfold tailWord_249913
  simp only [CollatzResearch.WordTrace]
  refine ⟨9115075943615357587442393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6076717295743571724961595 9115075943615357587442393)
  ·
    refine ⟨6836306957711518190581795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9115075943615357587442393 6836306957711518190581795)
    ·
      refine ⟨10254460436567277285872693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6836306957711518190581795 10254460436567277285872693)
      ·
        refine ⟨961355665928182245550565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10254460436567277285872693 961355665928182245550565)
        ·
          refine ⟨180254187361534171040731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 961355665928182245550565 180254187361534171040731)
          ·
            refine ⟨270381281042301256561097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180254187361534171040731 270381281042301256561097)
            ·
              refine ⟨202785960781725942420823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270381281042301256561097 202785960781725942420823)
              ·
                refine ⟨304178941172588913631235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202785960781725942420823 304178941172588913631235)
                ·
                  refine ⟨456268411758883370446853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304178941172588913631235 456268411758883370446853)
                  ·
                    refine ⟨85550327204790631958785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 456268411758883370446853 85550327204790631958785)
                    ·
                      rfl

theorem cell22_249913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 1, 4].length) (baseStart_249913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249913 prefixEnd_249913 := by exact prefixLift 249913
  have htrace : WordTrace (prefixWord ++ tailWord_249913) baseStart_249913 baseEnd_249913 := by
    simpa [prefixWord, tailWord_249913, baseEnd_249913] using wordTrace_append hprefix tailTrace_249913
  have hstable : (prefixWord ++ tailWord_249913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249913).length < 2 ^ (prefixWord ++ tailWord_249913).sum := by decide
  have hdescent : baseEnd_249913 < baseStart_249913 := by decide
  rcases family_descends (prefixWord ++ tailWord_249913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249926 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_249926 : Nat := 118140960795 + 249926 * 2 ^ 59
def prefixEnd_249926 : Nat := 4983230072969 + 3 ^ 40 * 249926 * 2
def baseEnd_249926 : Nat := 85554777370462931383745

theorem tailTrace_249926 : CollatzResearch.WordTrace tailWord_249926 prefixEnd_249926 85554777370462931383745 := by
  unfold tailWord_249926
  simp only [CollatzResearch.WordTrace]
  refine ⟨284860940392758150239551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6077033395045507205110421 284860940392758150239551)
  ·
    refine ⟨427291410589137225359327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284860940392758150239551 427291410589137225359327)
    ·
      refine ⟨640937115883705838038991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427291410589137225359327 640937115883705838038991)
      ·
        refine ⟨961405673825558757058487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640937115883705838038991 961405673825558757058487)
        ·
          refine ⟨1442108510738338135587731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961405673825558757058487 1442108510738338135587731)
          ·
            refine ⟨2163162766107507203381597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442108510738338135587731 2163162766107507203381597)
            ·
              refine ⟨811186037290315201268099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2163162766107507203381597 811186037290315201268099)
              ·
                refine ⟨1216779055935472801902149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811186037290315201268099 1216779055935472801902149)
                ·
                  refine ⟨228146072987901150356653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216779055935472801902149 228146072987901150356653)
                  ·
                    refine ⟨85554777370462931383745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 228146072987901150356653 85554777370462931383745)
                    ·
                      rfl

theorem cell22_249926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_249926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249926 prefixEnd_249926 := by exact prefixLift 249926
  have htrace : WordTrace (prefixWord ++ tailWord_249926) baseStart_249926 baseEnd_249926 := by
    simpa [prefixWord, tailWord_249926, baseEnd_249926] using wordTrace_append hprefix tailTrace_249926
  have hstable : (prefixWord ++ tailWord_249926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249926).length < 2 ^ (prefixWord ++ tailWord_249926).sum := by decide
  have hdescent : baseEnd_249926 < baseStart_249926 := by decide
  rcases family_descends (prefixWord ++ tailWord_249926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249988 : List Nat := [2, 3, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_249988 : Nat := 118140960795 + 249988 * 2 ^ 59
def prefixEnd_249988 : Nat := 4983230072969 + 3 ^ 40 * 249988 * 2
def baseEnd_249988 : Nat := 85576001237515436333555

theorem tailTrace_249988 : CollatzResearch.WordTrace tailWord_249988 prefixEnd_249988 85576001237515436333555 := by
  unfold tailWord_249988
  simp only [CollatzResearch.WordTrace]
  refine ⟨4558905709171822698211309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6078540945562430264281745 4558905709171822698211309)
  ·
    refine ⟨1709589640939433511829241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4558905709171822698211309 1709589640939433511829241)
    ·
      refine ⟨1282192230704575133871931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1709589640939433511829241 1282192230704575133871931)
      ·
        refine ⟨1923288346056862700807897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282192230704575133871931 1923288346056862700807897)
        ·
          refine ⟨1442466259542647025605923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1923288346056862700807897 1442466259542647025605923)
          ·
            refine ⟨2163699389313970538408885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442466259542647025605923 2163699389313970538408885)
            ·
              refine ⟨202846817748184737975833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2163699389313970538408885 202846817748184737975833)
              ·
                refine ⟨152135113311138553481875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202846817748184737975833 152135113311138553481875)
                ·
                  refine ⟨228202669966707830222813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152135113311138553481875 228202669966707830222813)
                  ·
                    refine ⟨85576001237515436333555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 228202669966707830222813 85576001237515436333555)
                    ·
                      rfl

theorem cell22_249988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_249988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_249988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_249988 prefixEnd_249988 := by exact prefixLift 249988
  have htrace : WordTrace (prefixWord ++ tailWord_249988) baseStart_249988 baseEnd_249988 := by
    simpa [prefixWord, tailWord_249988, baseEnd_249988] using wordTrace_append hprefix tailTrace_249988
  have hstable : (prefixWord ++ tailWord_249988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249988).length < 2 ^ (prefixWord ++ tailWord_249988).sum := by decide
  have hdescent : baseEnd_249988 < baseStart_249988 := by decide
  rcases family_descends (prefixWord ++ tailWord_249988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250012 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 8]
def baseStart_250012 : Nat := 118140960795 + 250012 * 2 ^ 59
def prefixEnd_250012 : Nat := 4983230072969 + 3 ^ 40 * 250012 * 2
def baseEnd_250012 : Nat := 28528072309329124577827

theorem tailTrace_250012 : CollatzResearch.WordTrace tailWord_250012 prefixEnd_250012 28528072309329124577827 := by
  unfold tailWord_250012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4559343385128348747648145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6079124513504464996864193 4559343385128348747648145)
  ·
    refine ⟨3419507538846261560736109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4559343385128348747648145 3419507538846261560736109)
    ·
      refine ⟨1282315327067348085276041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3419507538846261560736109 1282315327067348085276041)
      ·
        refine ⟨961736495300511063957031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1282315327067348085276041 961736495300511063957031)
        ·
          refine ⟨1442604742950766595935547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961736495300511063957031 1442604742950766595935547)
          ·
            refine ⟨2163907114426149893903321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442604742950766595935547 2163907114426149893903321)
            ·
              refine ⟨1622930335819612420427491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2163907114426149893903321 1622930335819612420427491)
              ·
                refine ⟨2434395503729418630641237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622930335819612420427491 2434395503729418630641237)
                ·
                  refine ⟨28528072309329124577827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2434395503729418630641237 28528072309329124577827)
                  ·
                    rfl

theorem cell22_250012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_250012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250012 prefixEnd_250012 := by exact prefixLift 250012
  have htrace : WordTrace (prefixWord ++ tailWord_250012) baseStart_250012 baseEnd_250012 := by
    simpa [prefixWord, tailWord_250012, baseEnd_250012] using wordTrace_append hprefix tailTrace_250012
  have hstable : (prefixWord ++ tailWord_250012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250012).length < 2 ^ (prefixWord ++ tailWord_250012).sum := by decide
  have hdescent : baseEnd_250012 < baseStart_250012 := by decide
  rcases family_descends (prefixWord ++ tailWord_250012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250106 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 3, 3]
def baseStart_250106 : Nat := 118140960795 + 250106 * 2 ^ 59
def prefixEnd_250106 : Nat := 4983230072969 + 3 ^ 40 * 250106 * 2
def baseEnd_250106 : Nat := 85616395049002461883193

theorem tailTrace_250106 : CollatzResearch.WordTrace tailWord_250106 prefixEnd_250106 85616395049002461883193 := by
  unfold tailWord_250106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2280528807979037887304543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6081410154610767699478781 2280528807979037887304543)
  ·
    refine ⟨3420793211968556830956815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2280528807979037887304543 3420793211968556830956815)
    ·
      refine ⟨5131189817952835246435223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3420793211968556830956815 5131189817952835246435223)
      ·
        refine ⟨7696784726929252869652835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5131189817952835246435223 7696784726929252869652835)
        ·
          refine ⟨11545177090393879304479253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7696784726929252869652835 11545177090393879304479253)
          ·
            refine ⟨541180176112213092397465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11545177090393879304479253 541180176112213092397465)
            ·
              refine ⟨405885132084159819298099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541180176112213092397465 405885132084159819298099)
              ·
                refine ⟨608827698126239728947149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405885132084159819298099 608827698126239728947149)
                ·
                  refine ⟨228310386797339898355181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608827698126239728947149 228310386797339898355181)
                  ·
                    refine ⟨85616395049002461883193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 228310386797339898355181 85616395049002461883193)
                    ·
                      rfl

theorem cell22_250106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_250106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250106 prefixEnd_250106 := by exact prefixLift 250106
  have htrace : WordTrace (prefixWord ++ tailWord_250106) baseStart_250106 baseEnd_250106 := by
    simpa [prefixWord, tailWord_250106, baseEnd_250106] using wordTrace_append hprefix tailTrace_250106
  have hstable : (prefixWord ++ tailWord_250106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250106).length < 2 ^ (prefixWord ++ tailWord_250106).sum := by decide
  have hdescent : baseEnd_250106 < baseStart_250106 := by decide
  rcases family_descends (prefixWord ++ tailWord_250106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250117 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_250117 : Nat := 118140960795 + 250117 * 2 ^ 59
def prefixEnd_250117 : Nat := 4983230072969 + 3 ^ 40 * 250117 * 2
def baseEnd_250117 : Nat := 85620160573802099858159

theorem tailTrace_250117 : CollatzResearch.WordTrace tailWord_250117 prefixEnd_250117 85620160573802099858159 := by
  unfold tailWord_250117
  simp only [CollatzResearch.WordTrace]
  refine ⟨9122516434876300427868605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6081677623250866951912403 9122516434876300427868605)
  ·
    refine ⟨3420943663078612660450727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9122516434876300427868605 3420943663078612660450727)
    ·
      refine ⟨5131415494617918990676091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3420943663078612660450727 5131415494617918990676091)
      ·
        refine ⟨7697123241926878486014137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5131415494617918990676091 7697123241926878486014137)
        ·
          refine ⟨5772842431445158864510603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7697123241926878486014137 5772842431445158864510603)
          ·
            refine ⟨8659263647167738296765905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5772842431445158864510603 8659263647167738296765905)
            ·
              refine ⟨6494447735375803722574429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8659263647167738296765905 6494447735375803722574429)
              ·
                refine ⟨2435417900765926395965411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6494447735375803722574429 2435417900765926395965411)
                ·
                  refine ⟨3653126851148889593948117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435417900765926395965411 3653126851148889593948117)
                  ·
                    refine ⟨85620160573802099858159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3653126851148889593948117 85620160573802099858159)
                    ·
                      rfl

theorem cell22_250117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_250117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250117 prefixEnd_250117 := by exact prefixLift 250117
  have htrace : WordTrace (prefixWord ++ tailWord_250117) baseStart_250117 baseEnd_250117 := by
    simpa [prefixWord, tailWord_250117, baseEnd_250117] using wordTrace_append hprefix tailTrace_250117
  have hstable : (prefixWord ++ tailWord_250117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250117).length < 2 ^ (prefixWord ++ tailWord_250117).sum := by decide
  have hdescent : baseEnd_250117 < baseStart_250117 := by decide
  rcases family_descends (prefixWord ++ tailWord_250117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250157 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_250157 : Nat := 118140960795 + 250157 * 2 ^ 59
def prefixEnd_250157 : Nat := 4983230072969 + 3 ^ 40 * 250157 * 2
def baseEnd_250157 : Nat := 85633853391255328858037

theorem tailTrace_250157 : CollatzResearch.WordTrace tailWord_250157 prefixEnd_250157 85633853391255328858037 := by
  unfold tailWord_250157
  simp only [CollatzResearch.WordTrace]
  refine ⟨9123975354731387259324725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6082650236487591506216483 9123975354731387259324725)
  ·
    refine ⟨855372689506067555561693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9123975354731387259324725 855372689506067555561693)
    ·
      refine ⟨320764758564775333335635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 855372689506067555561693 320764758564775333335635)
      ·
        refine ⟨481147137847163000003453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320764758564775333335635 481147137847163000003453)
        ·
          refine ⟨180430176692686125001295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481147137847163000003453 180430176692686125001295)
          ·
            refine ⟨270645265039029187501943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180430176692686125001295 270645265039029187501943)
            ·
              refine ⟨405967897558543781252915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270645265039029187501943 405967897558543781252915)
              ·
                refine ⟨608951846337815671879373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405967897558543781252915 608951846337815671879373)
                ·
                  refine ⟨228356942376680876954765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608951846337815671879373 228356942376680876954765)
                  ·
                    refine ⟨85633853391255328858037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 228356942376680876954765 85633853391255328858037)
                    ·
                      rfl

theorem cell22_250157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_250157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250157 prefixEnd_250157 := by exact prefixLift 250157
  have htrace : WordTrace (prefixWord ++ tailWord_250157) baseStart_250157 baseEnd_250157 := by
    simpa [prefixWord, tailWord_250157, baseEnd_250157] using wordTrace_append hprefix tailTrace_250157
  have hstable : (prefixWord ++ tailWord_250157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250157).length < 2 ^ (prefixWord ++ tailWord_250157).sum := by decide
  have hdescent : baseEnd_250157 < baseStart_250157 := by decide
  rcases family_descends (prefixWord ++ tailWord_250157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250194 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_250194 : Nat := 118140960795 + 250194 * 2 ^ 59
def prefixEnd_250194 : Nat := 4983230072969 + 3 ^ 40 * 250194 * 2
def baseEnd_250194 : Nat := 85646519247399565682923

theorem tailTrace_250194 : CollatzResearch.WordTrace tailWord_250194 prefixEnd_250194 85646519247399565682923 := by
  unfold tailWord_250194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281331213899335644605409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6083549903731561718947757 2281331213899335644605409)
  ·
    refine ⟨1710998410424501733454057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2281331213899335644605409 1710998410424501733454057)
    ·
      refine ⟨1283248807818376300090543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1710998410424501733454057 1283248807818376300090543)
      ·
        refine ⟨1924873211727564450135815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283248807818376300090543 1924873211727564450135815)
        ·
          refine ⟨2887309817591346675203723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924873211727564450135815 2887309817591346675203723)
          ·
            refine ⟨4330964726387020012805585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887309817591346675203723 4330964726387020012805585)
            ·
              refine ⟨3248223544790265009604189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4330964726387020012805585 3248223544790265009604189)
              ·
                refine ⟨1218083829296349378601571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3248223544790265009604189 1218083829296349378601571)
                ·
                  refine ⟨1827125743944524067902357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1218083829296349378601571 1827125743944524067902357)
                  ·
                    refine ⟨85646519247399565682923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1827125743944524067902357 85646519247399565682923)
                    ·
                      rfl

theorem cell22_250194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_250194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250194 prefixEnd_250194 := by exact prefixLift 250194
  have htrace : WordTrace (prefixWord ++ tailWord_250194) baseStart_250194 baseEnd_250194 := by
    simpa [prefixWord, tailWord_250194, baseEnd_250194] using wordTrace_append hprefix tailTrace_250194
  have hstable : (prefixWord ++ tailWord_250194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250194).length < 2 ^ (prefixWord ++ tailWord_250194).sum := by decide
  have hdescent : baseEnd_250194 < baseStart_250194 := by decide
  rcases family_descends (prefixWord ++ tailWord_250194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250196 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_250196 : Nat := 118140960795 + 250196 * 2 ^ 59
def prefixEnd_250196 : Nat := 4983230072969 + 3 ^ 40 * 250196 * 2
def baseEnd_250196 : Nat := 85647203888272227132917

theorem tailTrace_250196 : CollatzResearch.WordTrace tailWord_250196 prefixEnd_250196 85647203888272227132917 := by
  unfold tailWord_250196
  simp only [CollatzResearch.WordTrace]
  refine ⟨4562698900795048459997221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6083598534393397946662961 4562698900795048459997221)
  ·
    refine ⟨855506043899071586249479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4562698900795048459997221 855506043899071586249479)
    ·
      refine ⟨1283259065848607379374219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 855506043899071586249479 1283259065848607379374219)
      ·
        refine ⟨1924888598772911069061329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283259065848607379374219 1924888598772911069061329)
        ·
          refine ⟨1443666449079683301795997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1924888598772911069061329 1443666449079683301795997)
          ·
            refine ⟨541374918404881238173499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1443666449079683301795997 541374918404881238173499)
            ·
              refine ⟨812062377607321857260249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541374918404881238173499 812062377607321857260249)
              ·
                refine ⟨609046783205491392945187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812062377607321857260249 609046783205491392945187)
                ·
                  refine ⟨913570174808237089417781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609046783205491392945187 913570174808237089417781)
                  ·
                    refine ⟨85647203888272227132917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 913570174808237089417781 85647203888272227132917)
                    ·
                      rfl

theorem cell22_250196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_250196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250196 prefixEnd_250196 := by exact prefixLift 250196
  have htrace : WordTrace (prefixWord ++ tailWord_250196) baseStart_250196 baseEnd_250196 := by
    simpa [prefixWord, tailWord_250196, baseEnd_250196] using wordTrace_append hprefix tailTrace_250196
  have hstable : (prefixWord ++ tailWord_250196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250196).length < 2 ^ (prefixWord ++ tailWord_250196).sum := by decide
  have hdescent : baseEnd_250196 < baseStart_250196 := by decide
  rcases family_descends (prefixWord ++ tailWord_250196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250213 : List Nat := [1, 3, 1, 3, 1, 4, 2, 2, 2, 3]
def baseStart_250213 : Nat := 118140960795 + 250213 * 2 ^ 59
def prefixEnd_250213 : Nat := 4983230072969 + 3 ^ 40 * 250213 * 2
def baseEnd_250213 : Nat := 85653023335689849457865

theorem tailTrace_250213 : CollatzResearch.WordTrace tailWord_250213 prefixEnd_250213 85653023335689849457865 := by
  unfold tailWord_250213
  simp only [CollatzResearch.WordTrace]
  refine ⟨9126017842528508823363293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6084011895019005882242195 9126017842528508823363293)
  ·
    refine ⟨3422256690948190808761235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9126017842528508823363293 3422256690948190808761235)
    ·
      refine ⟨5133385036422286213141853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3422256690948190808761235 5133385036422286213141853)
      ·
        refine ⟨1925019388658357329928195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5133385036422286213141853 1925019388658357329928195)
        ·
          refine ⟨2887529082987535994892293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925019388658357329928195 2887529082987535994892293)
          ·
            refine ⟨541411703060162999042305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2887529082987535994892293 541411703060162999042305)
            ·
              refine ⟨406058777295122249281729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541411703060162999042305 406058777295122249281729)
              ·
                refine ⟨304544082971341686961297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406058777295122249281729 304544082971341686961297)
                ·
                  refine ⟨228408062228506265220973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304544082971341686961297 228408062228506265220973)
                  ·
                    refine ⟨85653023335689849457865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 228408062228506265220973 85653023335689849457865)
                    ·
                      rfl

theorem cell22_250213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_250213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250213 prefixEnd_250213 := by exact prefixLift 250213
  have htrace : WordTrace (prefixWord ++ tailWord_250213) baseStart_250213 baseEnd_250213 := by
    simpa [prefixWord, tailWord_250213, baseEnd_250213] using wordTrace_append hprefix tailTrace_250213
  have hstable : (prefixWord ++ tailWord_250213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250213).length < 2 ^ (prefixWord ++ tailWord_250213).sum := by decide
  have hdescent : baseEnd_250213 < baseStart_250213 := by decide
  rcases family_descends (prefixWord ++ tailWord_250213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250215 : List Nat := [1, 1, 5, 1, 3, 3, 2, 2, 4]
def baseStart_250215 : Nat := 118140960795 + 250215 * 2 ^ 59
def prefixEnd_250215 : Nat := 4983230072969 + 3 ^ 40 * 250215 * 2
def baseEnd_250215 : Nat := 28551235992187503635953

theorem tailTrace_250215 : CollatzResearch.WordTrace tailWord_250215 prefixEnd_250215 28551235992187503635953 := by
  unfold tailWord_250215
  simp only [CollatzResearch.WordTrace]
  refine ⟨9126090788521263164936099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6084060525680842109957399 9126090788521263164936099)
  ·
    refine ⟨13689136182781894747404149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9126090788521263164936099 13689136182781894747404149)
    ·
      refine ⟨1283356517135802632569139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13689136182781894747404149 1283356517135802632569139)
      ·
        refine ⟨1925034775703703948853709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283356517135802632569139 1925034775703703948853709)
        ·
          refine ⟨721888040888888980820141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1925034775703703948853709 721888040888888980820141)
          ·
            refine ⟨270708015333333367807553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 721888040888888980820141 270708015333333367807553)
            ·
              refine ⟨203031011500000025855665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270708015333333367807553 203031011500000025855665)
              ·
                refine ⟨152273258625000019391749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203031011500000025855665 152273258625000019391749)
                ·
                  refine ⟨28551235992187503635953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152273258625000019391749 28551235992187503635953)
                  ·
                    rfl

theorem cell22_250215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 4].length) (baseStart_250215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250215 prefixEnd_250215 := by exact prefixLift 250215
  have htrace : WordTrace (prefixWord ++ tailWord_250215) baseStart_250215 baseEnd_250215 := by
    simpa [prefixWord, tailWord_250215, baseEnd_250215] using wordTrace_append hprefix tailTrace_250215
  have hstable : (prefixWord ++ tailWord_250215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250215).length < 2 ^ (prefixWord ++ tailWord_250215).sum := by decide
  have hdescent : baseEnd_250215 < baseStart_250215 := by decide
  rcases family_descends (prefixWord ++ tailWord_250215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250226 : List Nat := [3, 2, 1, 2, 1, 5, 1, 7]
def baseStart_250226 : Nat := 118140960795 + 250226 * 2 ^ 59
def prefixEnd_250226 : Nat := 4983230072969 + 3 ^ 40 * 250226 * 2
def baseEnd_250226 : Nat := 9517497055706905431425

theorem tailTrace_250226 : CollatzResearch.WordTrace tailWord_250226 prefixEnd_250226 9517497055706905431425 := by
  unfold tailWord_250226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281622997870353010896633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6084327994320941362391021 2281622997870353010896633)
  ·
    refine ⟨1711217248402764758172475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2281622997870353010896633 1711217248402764758172475)
    ·
      refine ⟨2566825872604147137258713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1711217248402764758172475 2566825872604147137258713)
      ·
        refine ⟨1925119404453110352944035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2566825872604147137258713 1925119404453110352944035)
        ·
          refine ⟨2887679106679665529416053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925119404453110352944035 2887679106679665529416053)
          ·
            refine ⟨270719916251218643382755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2887679106679665529416053 270719916251218643382755)
            ·
              refine ⟨406079874376827965074133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270719916251218643382755 406079874376827965074133)
              ·
                refine ⟨9517497055706905431425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 406079874376827965074133 9517497055706905431425)
                ·
                  rfl

theorem cell22_250226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_250226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250226 prefixEnd_250226 := by exact prefixLift 250226
  have htrace : WordTrace (prefixWord ++ tailWord_250226) baseStart_250226 baseEnd_250226 := by
    simpa [prefixWord, tailWord_250226, baseEnd_250226] using wordTrace_append hprefix tailTrace_250226
  have hstable : (prefixWord ++ tailWord_250226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250226).length < 2 ^ (prefixWord ++ tailWord_250226).sum := by decide
  have hdescent : baseEnd_250226 < baseStart_250226 := by decide
  rcases family_descends (prefixWord ++ tailWord_250226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250230 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_250230 : Nat := 118140960795 + 250230 * 2 ^ 59
def prefixEnd_250230 : Nat := 4983230072969 + 3 ^ 40 * 250230 * 2
def baseEnd_250230 : Nat := 85658842783107471782813

theorem tailTrace_250230 : CollatzResearch.WordTrace tailWord_250230 prefixEnd_250230 85658842783107471782813 := by
  unfold tailWord_250230
  simp only [CollatzResearch.WordTrace]
  refine ⟨570414867716682545420759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6084425255644613817821429 570414867716682545420759)
  ·
    refine ⟨855622301575023818131139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 570414867716682545420759 855622301575023818131139)
    ·
      refine ⟨1283433452362535727196709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 855622301575023818131139 1283433452362535727196709)
      ·
        refine ⟨240643772317975448849383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1283433452362535727196709 240643772317975448849383)
        ·
          refine ⟨360965658476963173274075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240643772317975448849383 360965658476963173274075)
          ·
            refine ⟨541448487715444759911113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360965658476963173274075 541448487715444759911113)
            ·
              refine ⟨406086365786583569933335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541448487715444759911113 406086365786583569933335)
              ·
                refine ⟨609129548679875354900003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406086365786583569933335 609129548679875354900003)
                ·
                  refine ⟨913694323019813032350005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609129548679875354900003 913694323019813032350005)
                  ·
                    refine ⟨85658842783107471782813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 913694323019813032350005 85658842783107471782813)
                    ·
                      rfl

theorem cell22_250230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_250230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250230 prefixEnd_250230 := by exact prefixLift 250230
  have htrace : WordTrace (prefixWord ++ tailWord_250230) baseStart_250230 baseEnd_250230 := by
    simpa [prefixWord, tailWord_250230, baseEnd_250230] using wordTrace_append hprefix tailTrace_250230
  have hstable : (prefixWord ++ tailWord_250230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250230).length < 2 ^ (prefixWord ++ tailWord_250230).sum := by decide
  have hdescent : baseEnd_250230 < baseStart_250230 := by decide
  rcases family_descends (prefixWord ++ tailWord_250230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250348 : List Nat := [2, 2, 1, 1, 2, 1, 5, 3, 2, 3]
def baseStart_250348 : Nat := 118140960795 + 250348 * 2 ^ 59
def prefixEnd_250348 : Nat := 4983230072969 + 3 ^ 40 * 250348 * 2
def baseEnd_250348 : Nat := 85699236594594497332451

theorem tailTrace_250348 : CollatzResearch.WordTrace tailWord_250348 prefixEnd_250348 85699236594594497332451 := by
  unfold tailWord_250348
  simp only [CollatzResearch.WordTrace]
  refine ⟨4565470848519713439763849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6087294464692951253018465 4565470848519713439763849)
  ·
    refine ⟨3424103136389785079822887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4565470848519713439763849 3424103136389785079822887)
    ·
      refine ⟨5136154704584677619734331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3424103136389785079822887 5136154704584677619734331)
      ·
        refine ⟨7704232056877016429601497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5136154704584677619734331 7704232056877016429601497)
        ·
          refine ⟨5778174042657762322201123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7704232056877016429601497 5778174042657762322201123)
          ·
            refine ⟨8667261063986643483301685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5778174042657762322201123 8667261063986643483301685)
            ·
              refine ⟨812555724748747826559533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8667261063986643483301685 812555724748747826559533)
              ·
                refine ⟨304708396780780434959825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 812555724748747826559533 304708396780780434959825)
                ·
                  refine ⟨228531297585585326219869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304708396780780434959825 228531297585585326219869)
                  ·
                    refine ⟨85699236594594497332451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 228531297585585326219869 85699236594594497332451)
                    ·
                      rfl

theorem cell22_250348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_250348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250348 prefixEnd_250348 := by exact prefixLift 250348
  have htrace : WordTrace (prefixWord ++ tailWord_250348) baseStart_250348 baseEnd_250348 := by
    simpa [prefixWord, tailWord_250348, baseEnd_250348] using wordTrace_append hprefix tailTrace_250348
  have hstable : (prefixWord ++ tailWord_250348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250348).length < 2 ^ (prefixWord ++ tailWord_250348).sum := by decide
  have hdescent : baseEnd_250348 < baseStart_250348 := by decide
  rcases family_descends (prefixWord ++ tailWord_250348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250410 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 3, 3]
def baseStart_250410 : Nat := 118140960795 + 250410 * 2 ^ 59
def prefixEnd_250410 : Nat := 4983230072969 + 3 ^ 40 * 250410 * 2
def baseEnd_250410 : Nat := 85720460461647002282261

theorem tailTrace_250410 : CollatzResearch.WordTrace tailWord_250410 prefixEnd_250410 85720460461647002282261 := by
  unfold tailWord_250410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283300755703702867071171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6088802015209874312189789 2283300755703702867071171)
  ·
    refine ⟨3424951133555554300606757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2283300755703702867071171 3424951133555554300606757)
    ·
      refine ⟨642178337541666431363767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3424951133555554300606757 642178337541666431363767)
      ·
        refine ⟨963267506312499647045651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642178337541666431363767 963267506312499647045651)
        ·
          refine ⟨1444901259468749470568477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963267506312499647045651 1444901259468749470568477)
          ·
            refine ⟨541837972300781051463179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1444901259468749470568477 541837972300781051463179)
            ·
              refine ⟨812756958451171577194769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541837972300781051463179 812756958451171577194769)
              ·
                refine ⟨609567718838378682896077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812756958451171577194769 609567718838378682896077)
                ·
                  refine ⟨228587894564392006086029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609567718838378682896077 228587894564392006086029)
                  ·
                    refine ⟨85720460461647002282261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 228587894564392006086029 85720460461647002282261)
                    ·
                      rfl

theorem cell22_250410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_250410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250410 prefixEnd_250410 := by exact prefixLift 250410
  have htrace : WordTrace (prefixWord ++ tailWord_250410) baseStart_250410 baseEnd_250410 := by
    simpa [prefixWord, tailWord_250410, baseEnd_250410] using wordTrace_append hprefix tailTrace_250410
  have hstable : (prefixWord ++ tailWord_250410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250410).length < 2 ^ (prefixWord ++ tailWord_250410).sum := by decide
  have hdescent : baseEnd_250410 < baseStart_250410 := by decide
  rcases family_descends (prefixWord ++ tailWord_250410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250421 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_250421 : Nat := 118140960795 + 250421 * 2 ^ 59
def prefixEnd_250421 : Nat := 4983230072969 + 3 ^ 40 * 250421 * 2
def baseEnd_250421 : Nat := 85724225986446640257227

theorem tailTrace_250421 : CollatzResearch.WordTrace tailWord_250421 prefixEnd_250421 85724225986446640257227 := by
  unfold tailWord_250421
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133604225774960346935117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6089069483849973564623411 9133604225774960346935117)
  ·
    refine ⟨3425101584665610130100669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9133604225774960346935117 3425101584665610130100669)
    ·
      refine ⟨1284413094249603798787751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3425101584665610130100669 1284413094249603798787751)
      ·
        refine ⟨1926619641374405698181627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284413094249603798787751 1926619641374405698181627)
        ·
          refine ⟨2889929462061608547272441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926619641374405698181627 2889929462061608547272441)
          ·
            refine ⟨2167447096546206410454331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2889929462061608547272441 2167447096546206410454331)
            ·
              refine ⟨3251170644819309615681497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167447096546206410454331 3251170644819309615681497)
              ·
                refine ⟨2438377983614482211761123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3251170644819309615681497 2438377983614482211761123)
                ·
                  refine ⟨3657566975421723317641685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438377983614482211761123 3657566975421723317641685)
                  ·
                    refine ⟨85724225986446640257227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3657566975421723317641685 85724225986446640257227)
                    ·
                      rfl

theorem cell22_250421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_250421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250421 prefixEnd_250421 := by exact prefixLift 250421
  have htrace : WordTrace (prefixWord ++ tailWord_250421) baseStart_250421 baseEnd_250421 := by
    simpa [prefixWord, tailWord_250421, baseEnd_250421] using wordTrace_append hprefix tailTrace_250421
  have hstable : (prefixWord ++ tailWord_250421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250421).length < 2 ^ (prefixWord ++ tailWord_250421).sum := by decide
  have hdescent : baseEnd_250421 < baseStart_250421 := by decide
  rcases family_descends (prefixWord ++ tailWord_250421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250496 : List Nat := [2, 1, 1, 2, 1, 5, 10]
def baseStart_250496 : Nat := 118140960795 + 250496 * 2 ^ 59
def prefixEnd_250496 : Nat := 4983230072969 + 3 ^ 40 * 250496 * 2
def baseEnd_250496 : Nat := 3175922222932275727111

theorem tailTrace_250496 : CollatzResearch.WordTrace tailWord_250496 prefixEnd_250496 3175922222932275727111 := by
  unfold tailWord_250496
  simp only [CollatzResearch.WordTrace]
  refine ⟨4568169850251624077957671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6090893133668832103943561 4568169850251624077957671)
  ·
    refine ⟨6852254775377436116936507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4568169850251624077957671 6852254775377436116936507)
    ·
      refine ⟨10278382163066154175404761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6852254775377436116936507 10278382163066154175404761)
      ·
        refine ⟨7708786622299615631553571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10278382163066154175404761 7708786622299615631553571)
        ·
          refine ⟨11563179933449423447330357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7708786622299615631553571 11563179933449423447330357)
          ·
            refine ⟨1084048118760883448187221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11563179933449423447330357 1084048118760883448187221)
            ·
              refine ⟨3175922222932275727111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1084048118760883448187221 3175922222932275727111)
              ·
                rfl

theorem cell22_250496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 10].length) (baseStart_250496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250496 prefixEnd_250496 := by exact prefixLift 250496
  have htrace : WordTrace (prefixWord ++ tailWord_250496) baseStart_250496 baseEnd_250496 := by
    simpa [prefixWord, tailWord_250496, baseEnd_250496] using wordTrace_append hprefix tailTrace_250496
  have hstable : (prefixWord ++ tailWord_250496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250496).length < 2 ^ (prefixWord ++ tailWord_250496).sum := by decide
  have hdescent : baseEnd_250496 < baseStart_250496 := by decide
  rcases family_descends (prefixWord ++ tailWord_250496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250500 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_250500 : Nat := 118140960795 + 250500 * 2 ^ 59
def prefixEnd_250500 : Nat := 4983230072969 + 3 ^ 40 * 250500 * 2
def baseEnd_250500 : Nat := 85751269300916767531985

theorem tailTrace_250500 : CollatzResearch.WordTrace tailWord_250500 prefixEnd_250500 85751269300916767531985 := by
  unfold tailWord_250500
  simp only [CollatzResearch.WordTrace]
  refine ⟨4568242796244378419530477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6090990394992504559373969 4568242796244378419530477)
  ·
    refine ⟨1713091048591641907323929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4568242796244378419530477 1713091048591641907323929)
    ·
      refine ⟨1284818286443731430492947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1713091048591641907323929 1284818286443731430492947)
      ·
        refine ⟨1927227429665597145739421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284818286443731430492947 1927227429665597145739421)
        ·
          refine ⟨722710286124598929652283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1927227429665597145739421 722710286124598929652283)
          ·
            refine ⟨1084065429186898394478425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722710286124598929652283 1084065429186898394478425)
            ·
              refine ⟨813049071890173795858819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084065429186898394478425 813049071890173795858819)
              ·
                refine ⟨1219573607835260693788229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813049071890173795858819 1219573607835260693788229)
                ·
                  refine ⟨228670051469111380085293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1219573607835260693788229 228670051469111380085293)
                  ·
                    refine ⟨85751269300916767531985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 228670051469111380085293 85751269300916767531985)
                    ·
                      rfl

theorem cell22_250500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_250500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250500 prefixEnd_250500 := by exact prefixLift 250500
  have htrace : WordTrace (prefixWord ++ tailWord_250500) baseStart_250500 baseEnd_250500 := by
    simpa [prefixWord, tailWord_250500, baseEnd_250500] using wordTrace_append hprefix tailTrace_250500
  have hstable : (prefixWord ++ tailWord_250500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250500).length < 2 ^ (prefixWord ++ tailWord_250500).sum := by decide
  have hdescent : baseEnd_250500 < baseStart_250500 := by decide
  rcases family_descends (prefixWord ++ tailWord_250500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250618 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_250618 : Nat := 118140960795 + 250618 * 2 ^ 59
def prefixEnd_250618 : Nat := 4983230072969 + 3 ^ 40 * 250618 * 2
def baseEnd_250618 : Nat := 85791663112403793081623

theorem tailTrace_250618 : CollatzResearch.WordTrace tailWord_250618 prefixEnd_250618 85791663112403793081623 := by
  unfold tailWord_250618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2285197351515315747964127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6093859604040841994571005 2285197351515315747964127)
  ·
    refine ⟨3427796027272973621946191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2285197351515315747964127 3427796027272973621946191)
    ·
      refine ⟨5141694040909460432919287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427796027272973621946191 5141694040909460432919287)
      ·
        refine ⟨7712541061364190649378931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5141694040909460432919287 7712541061364190649378931)
        ·
          refine ⟨11568811592046285974068397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7712541061364190649378931 11568811592046285974068397)
          ·
            refine ⟨4338304347017357240275649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11568811592046285974068397 4338304347017357240275649)
            ·
              refine ⟨3253728260263017930206737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4338304347017357240275649 3253728260263017930206737)
              ·
                refine ⟨2440296195197263447655053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3253728260263017930206737 2440296195197263447655053)
                ·
                  refine ⟨915111073198973792870645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2440296195197263447655053 915111073198973792870645)
                  ·
                    refine ⟨85791663112403793081623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 915111073198973792870645 85791663112403793081623)
                    ·
                      rfl

theorem cell22_250618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_250618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250618 prefixEnd_250618 := by exact prefixLift 250618
  have htrace : WordTrace (prefixWord ++ tailWord_250618) baseStart_250618 baseEnd_250618 := by
    simpa [prefixWord, tailWord_250618, baseEnd_250618] using wordTrace_append hprefix tailTrace_250618
  have hstable : (prefixWord ++ tailWord_250618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250618).length < 2 ^ (prefixWord ++ tailWord_250618).sum := by decide
  have hdescent : baseEnd_250618 < baseStart_250618 := by decide
  rcases family_descends (prefixWord ++ tailWord_250618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250620 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 6]
def baseStart_250620 : Nat := 118140960795 + 250620 * 2 ^ 59
def prefixEnd_250620 : Nat := 4983230072969 + 3 ^ 40 * 250620 * 2
def baseEnd_250620 : Nat := 28597449251092151510539

theorem tailTrace_250620 : CollatzResearch.WordTrace tailWord_250620 prefixEnd_250620 28597449251092151510539 := by
  unfold tailWord_250620
  simp only [CollatzResearch.WordTrace]
  refine ⟨4570431176027008666714657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6093908234702678222286209 4570431176027008666714657)
  ·
    refine ⟨3427823382020256500035993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4570431176027008666714657 3427823382020256500035993)
    ·
      refine ⟨2570867536515192375026995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3427823382020256500035993 2570867536515192375026995)
      ·
        refine ⟨3856301304772788562540493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2570867536515192375026995 3856301304772788562540493)
        ·
          refine ⟨1446112989289795710952685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3856301304772788562540493 1446112989289795710952685)
          ·
            refine ⟨542292370983673391607257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1446112989289795710952685 542292370983673391607257)
            ·
              refine ⟨406719278237755043705443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542292370983673391607257 406719278237755043705443)
              ·
                refine ⟨610078917356632565558165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406719278237755043705443 610078917356632565558165)
                ·
                  refine ⟨28597449251092151510539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 610078917356632565558165 28597449251092151510539)
                  ·
                    rfl

theorem cell22_250620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_250620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250620 prefixEnd_250620 := by exact prefixLift 250620
  have htrace : WordTrace (prefixWord ++ tailWord_250620) baseStart_250620 baseEnd_250620 := by
    simpa [prefixWord, tailWord_250620, baseEnd_250620] using wordTrace_append hprefix tailTrace_250620
  have hstable : (prefixWord ++ tailWord_250620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250620).length < 2 ^ (prefixWord ++ tailWord_250620).sum := by decide
  have hdescent : baseEnd_250620 < baseStart_250620 := by decide
  rcases family_descends (prefixWord ++ tailWord_250620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250633 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 1, 6]
def baseStart_250633 : Nat := 118140960795 + 250633 * 2 ^ 59
def prefixEnd_250633 : Nat := 4983230072969 + 3 ^ 40 * 250633 * 2
def baseEnd_250633 : Nat := 85796797918948753956577

theorem tailTrace_250633 : CollatzResearch.WordTrace tailWord_250633 prefixEnd_250633 85796797918948753956577 := by
  unfold tailWord_250633
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141336501006920553652553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6094224334004613702435035 9141336501006920553652553)
  ·
    refine ⟨6856002375755190415239415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9141336501006920553652553 6856002375755190415239415)
    ·
      refine ⟨10284003563632785622859123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6856002375755190415239415 10284003563632785622859123)
      ·
        refine ⟨15426005345449178434288685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10284003563632785622859123 15426005345449178434288685)
        ·
          refine ⟨5784752004543441912858257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15426005345449178434288685 5784752004543441912858257)
          ·
            refine ⟨4338564003407581434643693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5784752004543441912858257 4338564003407581434643693)
            ·
              refine ⟨1626961501277843037991385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4338564003407581434643693 1626961501277843037991385)
              ·
                refine ⟨1220221125958382278493539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626961501277843037991385 1220221125958382278493539)
                ·
                  refine ⟨1830331688937573417740309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220221125958382278493539 1830331688937573417740309)
                  ·
                    refine ⟨85796797918948753956577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1830331688937573417740309 85796797918948753956577)
                    ·
                      rfl

theorem cell22_250633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_250633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250633 prefixEnd_250633 := by exact prefixLift 250633
  have htrace : WordTrace (prefixWord ++ tailWord_250633) baseStart_250633 baseEnd_250633 := by
    simpa [prefixWord, tailWord_250633, baseEnd_250633] using wordTrace_append hprefix tailTrace_250633
  have hstable : (prefixWord ++ tailWord_250633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250633).length < 2 ^ (prefixWord ++ tailWord_250633).sum := by decide
  have hdescent : baseEnd_250633 < baseStart_250633 := by decide
  rcases family_descends (prefixWord ++ tailWord_250633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250650 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_250650 : Nat := 118140960795 + 250650 * 2 ^ 59
def prefixEnd_250650 : Nat := 4983230072969 + 3 ^ 40 * 250650 * 2
def baseEnd_250650 : Nat := 85802617366366376281525

theorem tailTrace_250650 : CollatzResearch.WordTrace tailWord_250650 prefixEnd_250650 85802617366366376281525 := by
  unfold tailWord_250650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2285489135486333114255351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6094637694630221638014269 2285489135486333114255351)
  ·
    refine ⟨3428233703229499671383027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2285489135486333114255351 3428233703229499671383027)
    ·
      refine ⟨5142350554844249507074541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3428233703229499671383027 5142350554844249507074541)
      ·
        refine ⟨1928381458066593565152953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5142350554844249507074541 1928381458066593565152953)
        ·
          refine ⟨1446286093549945173864715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1928381458066593565152953 1446286093549945173864715)
          ·
            refine ⟨2169429140324917760797073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446286093549945173864715 2169429140324917760797073)
            ·
              refine ⟨1627071855243688320597805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2169429140324917760797073 1627071855243688320597805)
              ·
                refine ⟨610151945716383120224177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1627071855243688320597805 610151945716383120224177)
                ·
                  refine ⟨457613959287287340168133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610151945716383120224177 457613959287287340168133)
                  ·
                    refine ⟨85802617366366376281525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 457613959287287340168133 85802617366366376281525)
                    ·
                      rfl

theorem cell22_250650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_250650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250650 prefixEnd_250650 := by exact prefixLift 250650
  have htrace : WordTrace (prefixWord ++ tailWord_250650) baseStart_250650 baseEnd_250650 := by
    simpa [prefixWord, tailWord_250650, baseEnd_250650] using wordTrace_append hprefix tailTrace_250650
  have hstable : (prefixWord ++ tailWord_250650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250650).length < 2 ^ (prefixWord ++ tailWord_250650).sum := by decide
  have hdescent : baseEnd_250650 < baseStart_250650 := by decide
  rcases family_descends (prefixWord ++ tailWord_250650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250693 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 9]
def baseStart_250693 : Nat := 118140960795 + 250693 * 2 ^ 59
def prefixEnd_250693 : Nat := 4983230072969 + 3 ^ 40 * 250693 * 2
def baseEnd_250693 : Nat := 28605779048376199152131

theorem tailTrace_250693 : CollatzResearch.WordTrace tailWord_250693 prefixEnd_250693 28605779048376199152131 := by
  unfold tailWord_250693
  simp only [CollatzResearch.WordTrace]
  refine ⟨9143524880789550800836733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6095683253859700533891155 9143524880789550800836733)
  ·
    refine ⟨3428821830296081550313775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9143524880789550800836733 3428821830296081550313775)
    ·
      refine ⟨5143232745444122325470663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3428821830296081550313775 5143232745444122325470663)
      ·
        refine ⟨7714849118166183488205995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5143232745444122325470663 7714849118166183488205995)
        ·
          refine ⟨11572273677249275232308993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7714849118166183488205995 11572273677249275232308993)
          ·
            refine ⟨8679205257936956424231745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11572273677249275232308993 8679205257936956424231745)
            ·
              refine ⟨6509403943452717318173809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8679205257936956424231745 6509403943452717318173809)
              ·
                refine ⟨4882052957589537988630357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6509403943452717318173809 4882052957589537988630357)
                ·
                  refine ⟨28605779048376199152131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4882052957589537988630357 28605779048376199152131)
                  ·
                    rfl

theorem cell22_250693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_250693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250693 prefixEnd_250693 := by exact prefixLift 250693
  have htrace : WordTrace (prefixWord ++ tailWord_250693) baseStart_250693 baseEnd_250693 := by
    simpa [prefixWord, tailWord_250693, baseEnd_250693] using wordTrace_append hprefix tailTrace_250693
  have hstable : (prefixWord ++ tailWord_250693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250693).length < 2 ^ (prefixWord ++ tailWord_250693).sum := by decide
  have hdescent : baseEnd_250693 < baseStart_250693 := by decide
  rcases family_descends (prefixWord ++ tailWord_250693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
