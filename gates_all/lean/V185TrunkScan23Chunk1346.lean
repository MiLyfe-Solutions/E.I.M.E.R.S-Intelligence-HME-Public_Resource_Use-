import V185TrunkScan23Chunk1345

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7971096 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 3, 2, 2]
def baseStart_7971096 : Nat := 118140960795 + 7971096 * 2 ^ 59
def prefixEnd_7971096 : Nat := 4983230072969 + 3 ^ 40 * 7971096 * 2
def baseEnd_7971096 : Nat := 4093003591131250283941603

theorem tailTrace_7971096 : CollatzResearch.WordTrace tailWord_7971096 prefixEnd_7971096 4093003591131250283941603 := by
  unfold tailWord_7971096
  simp only [CollatzResearch.WordTrace]
  refine ⟨145364877765044010829458571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193819837020058681105944761 145364877765044010829458571)
  ·
    refine ⟨218047316647566016244187857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145364877765044010829458571 218047316647566016244187857)
    ·
      refine ⟨163535487485674512183140893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218047316647566016244187857 163535487485674512183140893)
      ·
        refine ⟨61325807807127942068677835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163535487485674512183140893 61325807807127942068677835)
        ·
          refine ⟨91988711710691913103016753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61325807807127942068677835 91988711710691913103016753)
          ·
            refine ⟨68991533783018934827262565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91988711710691913103016753 68991533783018934827262565)
            ·
              refine ⟨12935912584316050280111731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68991533783018934827262565 12935912584316050280111731)
              ·
                refine ⟨19403868876474075420167597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12935912584316050280111731 19403868876474075420167597)
                ·
                  refine ⟨7276450828677778282562849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19403868876474075420167597 7276450828677778282562849)
                  ·
                    refine ⟨5457338121508333711922137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7276450828677778282562849 5457338121508333711922137)
                    ·
                      refine ⟨4093003591131250283941603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457338121508333711922137 4093003591131250283941603)
                      ·
                        rfl

theorem cell23_7971096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_7971096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971096 prefixEnd_7971096 := by exact prefixLift 7971096
  have htrace : WordTrace (prefixWord ++ tailWord_7971096) baseStart_7971096 baseEnd_7971096 := by
    simpa [prefixWord, tailWord_7971096, baseEnd_7971096] using wordTrace_append hprefix tailTrace_7971096
  have hstable : (prefixWord ++ tailWord_7971096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971096).length < 2 ^ (prefixWord ++ tailWord_7971096).sum := by decide
  have hdescent : baseEnd_7971096 < baseStart_7971096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971130 : List Nat := [3, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2]
def baseStart_7971130 : Nat := 118140960795 + 7971130 * 2 ^ 59
def prefixEnd_7971130 : Nat := 4983230072969 + 3 ^ 40 * 7971130 * 2
def baseEnd_7971130 : Nat := 4093021049473503150916447

theorem tailTrace_7971130 : CollatzResearch.WordTrace tailWord_7971130 prefixEnd_7971130 4093021049473503150916447 := by
  unfold tailWord_7971130
  simp only [CollatzResearch.WordTrace]
  refine ⟨72682748902991211366413711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193820663741309896977103229 72682748902991211366413711)
  ·
    refine ⟨109024123354486817049620567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72682748902991211366413711 109024123354486817049620567)
    ·
      refine ⟨163536185031730225574430851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109024123354486817049620567 163536185031730225574430851)
      ·
        refine ⟨245304277547595338361646277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163536185031730225574430851 245304277547595338361646277)
        ·
          refine ⟨45994552040174125942808677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245304277547595338361646277 45994552040174125942808677)
          ·
            refine ⟨8623978507532648614276627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45994552040174125942808677 8623978507532648614276627)
            ·
              refine ⟨12935967761298972921414941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8623978507532648614276627 12935967761298972921414941)
              ·
                refine ⟨4850987910487114845530603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12935967761298972921414941 4850987910487114845530603)
                ·
                  refine ⟨7276481865730672268295905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850987910487114845530603 7276481865730672268295905)
                  ·
                    refine ⟨5457361399298004201221929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7276481865730672268295905 5457361399298004201221929)
                    ·
                      refine ⟨4093021049473503150916447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457361399298004201221929 4093021049473503150916447)
                      ·
                        rfl

theorem cell23_7971130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2].length) (baseStart_7971130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971130 prefixEnd_7971130 := by exact prefixLift 7971130
  have htrace : WordTrace (prefixWord ++ tailWord_7971130) baseStart_7971130 baseEnd_7971130 := by
    simpa [prefixWord, tailWord_7971130, baseEnd_7971130] using wordTrace_append hprefix tailTrace_7971130
  have hstable : (prefixWord ++ tailWord_7971130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971130).length < 2 ^ (prefixWord ++ tailWord_7971130).sum := by decide
  have hdescent : baseEnd_7971130 < baseStart_7971130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971172 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_7971172 : Nat := 118140960795 + 7971172 * 2 ^ 59
def prefixEnd_7971172 : Nat := 4983230072969 + 3 ^ 40 * 7971172 * 2
def baseEnd_7971172 : Nat := 4093042615660991986591253

theorem tailTrace_7971172 : CollatzResearch.WordTrace tailWord_7971172 prefixEnd_7971172 4093042615660991986591253 := by
  unfold tailWord_7971172
  simp only [CollatzResearch.WordTrace]
  refine ⟨145366263738906343319341885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193821684985208457759122513 145366263738906343319341885)
  ·
    refine ⟨54512348902089878744753207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145366263738906343319341885 54512348902089878744753207)
    ·
      refine ⟨81768523353134818117129811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54512348902089878744753207 81768523353134818117129811)
      ·
        refine ⟨122652785029702227175694717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81768523353134818117129811 122652785029702227175694717)
        ·
          refine ⟨45994794386138335190885519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122652785029702227175694717 45994794386138335190885519)
          ·
            refine ⟨68992191579207502786328279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45994794386138335190885519 68992191579207502786328279)
            ·
              refine ⟨103488287368811254179492419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68992191579207502786328279 103488287368811254179492419)
              ·
                refine ⟨155232431053216881269238629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103488287368811254179492419 155232431053216881269238629)
                ·
                  refine ⟨29106080822478165237982243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155232431053216881269238629 29106080822478165237982243)
                  ·
                    refine ⟨43659121233717247856973365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29106080822478165237982243 43659121233717247856973365)
                    ·
                      refine ⟨4093042615660991986591253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43659121233717247856973365 4093042615660991986591253)
                      ·
                        rfl

theorem cell23_7971172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_7971172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971172 prefixEnd_7971172 := by exact prefixLift 7971172
  have htrace : WordTrace (prefixWord ++ tailWord_7971172) baseStart_7971172 baseEnd_7971172 := by
    simpa [prefixWord, tailWord_7971172, baseEnd_7971172] using wordTrace_append hprefix tailTrace_7971172
  have hstable : (prefixWord ++ tailWord_7971172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971172).length < 2 ^ (prefixWord ++ tailWord_7971172).sum := by decide
  have hdescent : baseEnd_7971172 < baseStart_7971172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971173 : List Nat := [1, 3, 1, 3, 1, 5, 1, 2, 1, 3, 2]
def baseStart_7971173 : Nat := 118140960795 + 7971173 * 2 ^ 59
def prefixEnd_7971173 : Nat := 4983230072969 + 3 ^ 40 * 7971173 * 2
def baseEnd_7971173 : Nat := 4093043129141646482678749

theorem tailTrace_7971173 : CollatzResearch.WordTrace tailWord_7971173 prefixEnd_7971173 4093043129141646482678749 := by
  unfold tailWord_7971173
  simp only [CollatzResearch.WordTrace]
  refine ⟨290732563950809063809470173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193821709300539375872980115 290732563950809063809470173)
  ·
    refine ⟨109024711481553398928551315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290732563950809063809470173 109024711481553398928551315)
    ·
      refine ⟨163537067222330098392826973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109024711481553398928551315 163537067222330098392826973)
      ·
        refine ⟨61326400208373786897310115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163537067222330098392826973 61326400208373786897310115)
        ·
          refine ⟨91989600312560680345965173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61326400208373786897310115 91989600312560680345965173)
          ·
            refine ⟨8624025029302563782434235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91989600312560680345965173 8624025029302563782434235)
            ·
              refine ⟨12936037543953845673651353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8624025029302563782434235 12936037543953845673651353)
              ·
                refine ⟨9702028157965384255238515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12936037543953845673651353 9702028157965384255238515)
                ·
                  refine ⟨14553042236948076382857773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9702028157965384255238515 14553042236948076382857773)
                  ·
                    refine ⟨5457390838855528643571665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14553042236948076382857773 5457390838855528643571665)
                    ·
                      refine ⟨4093043129141646482678749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457390838855528643571665 4093043129141646482678749)
                      ·
                        rfl

theorem cell23_7971173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_7971173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971173 prefixEnd_7971173 := by exact prefixLift 7971173
  have htrace : WordTrace (prefixWord ++ tailWord_7971173) baseStart_7971173 baseEnd_7971173 := by
    simpa [prefixWord, tailWord_7971173, baseEnd_7971173] using wordTrace_append hprefix tailTrace_7971173
  have hstable : (prefixWord ++ tailWord_7971173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971173).length < 2 ^ (prefixWord ++ tailWord_7971173).sum := by decide
  have hdescent : baseEnd_7971173 < baseStart_7971173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971186 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 1, 4, 2]
def baseStart_7971186 : Nat := 118140960795 + 7971186 * 2 ^ 59
def prefixEnd_7971186 : Nat := 4983230072969 + 3 ^ 40 * 7971186 * 2
def baseEnd_7971186 : Nat := 4093049804390154931816189

theorem tailTrace_7971186 : CollatzResearch.WordTrace tailWord_7971186 prefixEnd_7971186 4093049804390154931816189 := by
  unfold tailWord_7971186
  simp only [CollatzResearch.WordTrace]
  refine ⟨72683259524940491757423353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193822025399841311353128941 72683259524940491757423353)
  ·
    refine ⟨54512444643705368818067515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72683259524940491757423353 54512444643705368818067515)
    ·
      refine ⟨81768666965558053227101273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54512444643705368818067515 81768666965558053227101273)
      ·
        refine ⟨61326500224168539920325955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81768666965558053227101273 61326500224168539920325955)
        ·
          refine ⟨91989750336252809880488933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61326500224168539920325955 91989750336252809880488933)
          ·
            refine ⟨17248078188047401852591675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91989750336252809880488933 17248078188047401852591675)
            ·
              refine ⟨25872117282071102778887513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17248078188047401852591675 25872117282071102778887513)
              ·
                refine ⟨19404087961553327084165635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25872117282071102778887513 19404087961553327084165635)
                ·
                  refine ⟨29106131942329990626248453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19404087961553327084165635 29106131942329990626248453)
                  ·
                    refine ⟨5457399739186873242421585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29106131942329990626248453 5457399739186873242421585)
                    ·
                      refine ⟨4093049804390154931816189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457399739186873242421585 4093049804390154931816189)
                      ·
                        rfl

theorem cell23_7971186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_7971186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971186 prefixEnd_7971186 := by exact prefixLift 7971186
  have htrace : WordTrace (prefixWord ++ tailWord_7971186) baseStart_7971186 baseEnd_7971186 := by
    simpa [prefixWord, tailWord_7971186, baseEnd_7971186] using wordTrace_append hprefix tailTrace_7971186
  have hstable : (prefixWord ++ tailWord_7971186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971186).length < 2 ^ (prefixWord ++ tailWord_7971186).sum := by decide
  have hdescent : baseEnd_7971186 < baseStart_7971186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971189 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_7971189 : Nat := 118140960795 + 7971189 * 2 ^ 59
def prefixEnd_7971189 : Nat := 4983230072969 + 3 ^ 40 * 7971189 * 2
def baseEnd_7971189 : Nat := 4093051344832118420078675

theorem tailTrace_7971189 : CollatzResearch.WordTrace tailWord_7971189 prefixEnd_7971189 4093051344832118420078675 := by
  unfold tailWord_7971189
  simp only [CollatzResearch.WordTrace]
  refine ⟨290733147518751098542052621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193822098345834065694701747 290733147518751098542052621)
  ·
    refine ⟨109024930319531661953269733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290733147518751098542052621 109024930319531661953269733)
    ·
      refine ⟨20442174434912186616238075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109024930319531661953269733 20442174434912186616238075)
      ·
        refine ⟨30663261652368279924357113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20442174434912186616238075 30663261652368279924357113)
        ·
          refine ⟨22997446239276209943267835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30663261652368279924357113 22997446239276209943267835)
          ·
            refine ⟨34496169358914314914901753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22997446239276209943267835 34496169358914314914901753)
            ·
              refine ⟨25872127019185736186176315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34496169358914314914901753 25872127019185736186176315)
              ·
                refine ⟨38808190528778604279264473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25872127019185736186176315 38808190528778604279264473)
                ·
                  refine ⟨29106142896583953209448355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38808190528778604279264473 29106142896583953209448355)
                  ·
                    refine ⟨43659214344875929814172533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29106142896583953209448355 43659214344875929814172533)
                    ·
                      refine ⟨4093051344832118420078675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43659214344875929814172533 4093051344832118420078675)
                      ·
                        rfl

theorem cell23_7971189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_7971189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971189 prefixEnd_7971189 := by exact prefixLift 7971189
  have htrace : WordTrace (prefixWord ++ tailWord_7971189) baseStart_7971189 baseEnd_7971189 := by
    simpa [prefixWord, tailWord_7971189, baseEnd_7971189] using wordTrace_append hprefix tailTrace_7971189
  have hstable : (prefixWord ++ tailWord_7971189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971189).length < 2 ^ (prefixWord ++ tailWord_7971189).sum := by decide
  have hdescent : baseEnd_7971189 < baseStart_7971189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971239 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 1, 7]
def baseStart_7971239 : Nat := 118140960795 + 7971239 * 2 ^ 59
def prefixEnd_7971239 : Nat := 4983230072969 + 3 ^ 40 * 7971239 * 2
def baseEnd_7971239 : Nat := 1364359006288281074817815

theorem tailTrace_7971239 : CollatzResearch.WordTrace tailWord_7971239 prefixEnd_7971239 1364359006288281074817815 := by
  unfold tailWord_7971239
  simp only [CollatzResearch.WordTrace]
  refine ⟨290734971168569957081372771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193823314112379971387581847 290734971168569957081372771)
  ·
    refine ⟨436102456752854935622059157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290734971168569957081372771 436102456752854935622059157)
    ·
      refine ⟨20442302660290075107284023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 436102456752854935622059157 20442302660290075107284023)
      ·
        refine ⟨30663453990435112660926035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20442302660290075107284023 30663453990435112660926035)
        ·
          refine ⟨45995180985652668991389053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30663453990435112660926035 45995180985652668991389053)
          ·
            refine ⟨17248192869619750871770895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45995180985652668991389053 17248192869619750871770895)
            ·
              refine ⟨25872289304429626307656343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17248192869619750871770895 25872289304429626307656343)
              ·
                refine ⟨38808433956644439461484515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25872289304429626307656343 38808433956644439461484515)
                ·
                  refine ⟨58212650934966659192226773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38808433956644439461484515 58212650934966659192226773)
                  ·
                    refine ⟨1364359006288281074817815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58212650934966659192226773 1364359006288281074817815)
                    ·
                      rfl

theorem cell23_7971239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_7971239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971239 prefixEnd_7971239 := by exact prefixLift 7971239
  have htrace : WordTrace (prefixWord ++ tailWord_7971239) baseStart_7971239 baseEnd_7971239 := by
    simpa [prefixWord, tailWord_7971239, baseEnd_7971239] using wordTrace_append hprefix tailTrace_7971239
  have hstable : (prefixWord ++ tailWord_7971239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971239).length < 2 ^ (prefixWord ++ tailWord_7971239).sum := by decide
  have hdescent : baseEnd_7971239 < baseStart_7971239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971336 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 6, 3, 2]
def baseStart_7971336 : Nat := 118140960795 + 7971336 * 2 ^ 59
def prefixEnd_7971336 : Nat := 4983230072969 + 3 ^ 40 * 7971336 * 2
def baseEnd_7971336 : Nat := 4093126826488329344940499

theorem tailTrace_7971336 : CollatzResearch.WordTrace tailWord_7971336 prefixEnd_7971336 4093126826488329344940499 := by
  unfold tailWord_7971336
  simp only [CollatzResearch.WordTrace]
  refine ⟨145369254524609271323826931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193825672699479028431769241 145369254524609271323826931)
  ·
    refine ⟨218053881786913906985740397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145369254524609271323826931 218053881786913906985740397)
    ·
      refine ⟨81770205670092715119652649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218053881786913906985740397 81770205670092715119652649)
      ·
        refine ⟨61327654252569536339739487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81770205670092715119652649 61327654252569536339739487)
        ·
          refine ⟨91991481378854304509609231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61327654252569536339739487 91991481378854304509609231)
          ·
            refine ⟨137987222068281456764413847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91991481378854304509609231 137987222068281456764413847)
            ·
              refine ⟨206980833102422185146620771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137987222068281456764413847 206980833102422185146620771)
              ·
                refine ⟨310471249653633277719931157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206980833102422185146620771 310471249653633277719931157)
                ·
                  refine ⟨14553339827514059893121773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 310471249653633277719931157 14553339827514059893121773)
                  ·
                    refine ⟨5457502435317772459920665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14553339827514059893121773 5457502435317772459920665)
                    ·
                      refine ⟨4093126826488329344940499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457502435317772459920665 4093126826488329344940499)
                      ·
                        rfl

theorem cell23_7971336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_7971336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971336 prefixEnd_7971336 := by exact prefixLift 7971336
  have htrace : WordTrace (prefixWord ++ tailWord_7971336) baseStart_7971336 baseEnd_7971336 := by
    simpa [prefixWord, tailWord_7971336, baseEnd_7971336] using wordTrace_append hprefix tailTrace_7971336
  have hstable : (prefixWord ++ tailWord_7971336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971336).length < 2 ^ (prefixWord ++ tailWord_7971336).sum := by decide
  have hdescent : baseEnd_7971336 < baseStart_7971336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971363 : List Nat := [1, 1, 1, 4, 4, 2, 3, 1, 1, 5]
def baseStart_7971363 : Nat := 118140960795 + 7971363 * 2 ^ 59
def prefixEnd_7971363 : Nat := 4983230072969 + 3 ^ 40 * 7971363 * 2
def baseEnd_7971363 : Nat := 1364380230155333579767625

theorem tailTrace_7971363 : CollatzResearch.WordTrace tailWord_7971363 prefixEnd_7971363 1364380230155333579767625 := by
  unfold tailWord_7971363
  simp only [CollatzResearch.WordTrace]
  refine ⟨290739493820120726258886743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193826329213413817505924495 290739493820120726258886743)
  ·
    refine ⟨436109240730181089388330115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290739493820120726258886743 436109240730181089388330115)
    ·
      refine ⟨654163861095271634082495173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436109240730181089388330115 654163861095271634082495173)
      ·
        refine ⟨122655723955363431390467845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 654163861095271634082495173 122655723955363431390467845)
        ·
          refine ⟨22997948241630643385712721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122655723955363431390467845 22997948241630643385712721)
          ·
            refine ⟨17248461181222982539284541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22997948241630643385712721 17248461181222982539284541)
            ·
              refine ⟨6468172942958618452231703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17248461181222982539284541 6468172942958618452231703)
              ·
                refine ⟨9702259414437927678347555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6468172942958618452231703 9702259414437927678347555)
                ·
                  refine ⟨14553389121656891517521333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9702259414437927678347555 14553389121656891517521333)
                  ·
                    refine ⟨1364380230155333579767625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14553389121656891517521333 1364380230155333579767625)
                    ·
                      rfl

theorem cell23_7971363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 1, 5].length) (baseStart_7971363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971363 prefixEnd_7971363 := by exact prefixLift 7971363
  have htrace : WordTrace (prefixWord ++ tailWord_7971363) baseStart_7971363 baseEnd_7971363 := by
    simpa [prefixWord, tailWord_7971363, baseEnd_7971363] using wordTrace_append hprefix tailTrace_7971363
  have hstable : (prefixWord ++ tailWord_7971363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971363).length < 2 ^ (prefixWord ++ tailWord_7971363).sum := by decide
  have hdescent : baseEnd_7971363 < baseStart_7971363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971376 : List Nat := [2, 1, 1, 1, 2, 3, 3, 4, 2, 4]
def baseStart_7971376 : Nat := 118140960795 + 7971376 * 2 ^ 59
def prefixEnd_7971376 : Nat := 4983230072969 + 3 ^ 40 * 7971376 * 2
def baseEnd_7971376 : Nat := 1364382455238169729480105

theorem tailTrace_7971376 : CollatzResearch.WordTrace tailWord_7971376 prefixEnd_7971376 1364382455238169729480105 := by
  unfold tailWord_7971376
  simp only [CollatzResearch.WordTrace]
  refine ⟨145369983984536814739554991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193826645312715752986073321 145369983984536814739554991)
  ·
    refine ⟨218054975976805222109332487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145369983984536814739554991 218054975976805222109332487)
    ·
      refine ⟨327082463965207833163998731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218054975976805222109332487 327082463965207833163998731)
      ·
        refine ⟨490623695947811749745998097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327082463965207833163998731 490623695947811749745998097)
        ·
          refine ⟨367967771960858812309498573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490623695947811749745998097 367967771960858812309498573)
          ·
            refine ⟨137987914485322054616061965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367967771960858812309498573 137987914485322054616061965)
            ·
              refine ⟨51745467931995770481023237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137987914485322054616061965 51745467931995770481023237)
              ·
                refine ⟨9702275237249206965191857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51745467931995770481023237 9702275237249206965191857)
                ·
                  refine ⟨7276706427936905223893893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9702275237249206965191857 7276706427936905223893893)
                  ·
                    refine ⟨1364382455238169729480105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7276706427936905223893893 1364382455238169729480105)
                    ·
                      rfl

theorem cell23_7971376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 2, 4].length) (baseStart_7971376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971376 prefixEnd_7971376 := by exact prefixLift 7971376
  have htrace : WordTrace (prefixWord ++ tailWord_7971376) baseStart_7971376 baseEnd_7971376 := by
    simpa [prefixWord, tailWord_7971376, baseEnd_7971376] using wordTrace_append hprefix tailTrace_7971376
  have hstable : (prefixWord ++ tailWord_7971376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971376).length < 2 ^ (prefixWord ++ tailWord_7971376).sum := by decide
  have hdescent : baseEnd_7971376 < baseStart_7971376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971379 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 4]
def baseStart_7971379 : Nat := 118140960795 + 7971379 * 2 ^ 59
def prefixEnd_7971379 : Nat := 4983230072969 + 3 ^ 40 * 7971379 * 2
def baseEnd_7971379 : Nat := 4093148906156472676702801

theorem tailTrace_7971379 : CollatzResearch.WordTrace tailWord_7971379 prefixEnd_7971379 4093148906156472676702801 := by
  unfold tailWord_7971379
  simp only [CollatzResearch.WordTrace]
  refine ⟨290740077388062760991469191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193826718258708507327646127 290740077388062760991469191)
  ·
    refine ⟨436110116082094141487203787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290740077388062760991469191 436110116082094141487203787)
    ·
      refine ⟨654165174123141212230805681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436110116082094141487203787 654165174123141212230805681)
      ·
        refine ⟨490623880592355909173104261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654165174123141212230805681 490623880592355909173104261)
        ·
          refine ⟨91991977611066732969957049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490623880592355909173104261 91991977611066732969957049)
          ·
            refine ⟨68993983208300049727467787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91991977611066732969957049 68993983208300049727467787)
            ·
              refine ⟨103490974812450074591201681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68993983208300049727467787 103490974812450074591201681)
              ·
                refine ⟨77618231109337555943401261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103490974812450074591201681 77618231109337555943401261)
                ·
                  refine ⟨29106836666001583478775473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77618231109337555943401261 29106836666001583478775473)
                  ·
                    refine ⟨21830127499501187609081605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29106836666001583478775473 21830127499501187609081605)
                    ·
                      refine ⟨4093148906156472676702801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21830127499501187609081605 4093148906156472676702801)
                      ·
                        rfl

theorem cell23_7971379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_7971379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971379 prefixEnd_7971379 := by exact prefixLift 7971379
  have htrace : WordTrace (prefixWord ++ tailWord_7971379) baseStart_7971379 baseEnd_7971379 := by
    simpa [prefixWord, tailWord_7971379, baseEnd_7971379] using wordTrace_append hprefix tailTrace_7971379
  have hstable : (prefixWord ++ tailWord_7971379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971379).length < 2 ^ (prefixWord ++ tailWord_7971379).sum := by decide
  have hdescent : baseEnd_7971379 < baseStart_7971379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971383 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 3, 2, 2]
def baseStart_7971383 : Nat := 118140960795 + 7971383 * 2 ^ 59
def prefixEnd_7971383 : Nat := 4983230072969 + 3 ^ 40 * 7971383 * 2
def baseEnd_7971383 : Nat := 4093150960079090661052783

theorem tailTrace_7971383 : CollatzResearch.WordTrace tailWord_7971383 prefixEnd_7971383 4093150960079090661052783 := by
  unfold tailWord_7971383
  simp only [CollatzResearch.WordTrace]
  refine ⟨290740223280048269674614803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193826815520032179783076535 290740223280048269674614803)
  ·
    refine ⟨436110334920072404511922205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290740223280048269674614803 436110334920072404511922205)
    ·
      refine ⟨163541375595027151691970827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436110334920072404511922205 163541375595027151691970827)
      ·
        refine ⟨245312063392540727537956241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163541375595027151691970827 245312063392540727537956241)
        ·
          refine ⟨183984047544405545653467181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245312063392540727537956241 183984047544405545653467181)
          ·
            refine ⟨68994017829152079620050193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183984047544405545653467181 68994017829152079620050193)
            ·
              refine ⟨51745513371864059715037645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68994017829152079620050193 51745513371864059715037645)
              ·
                refine ⟨19404567514449022393139117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51745513371864059715037645 19404567514449022393139117)
                ·
                  refine ⟨7276712817918383397427169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19404567514449022393139117 7276712817918383397427169)
                  ·
                    refine ⟨5457534613438787548070377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7276712817918383397427169 5457534613438787548070377)
                    ·
                      refine ⟨4093150960079090661052783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457534613438787548070377 4093150960079090661052783)
                      ·
                        rfl

theorem cell23_7971383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 2, 2].length) (baseStart_7971383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971383 prefixEnd_7971383 := by exact prefixLift 7971383
  have htrace : WordTrace (prefixWord ++ tailWord_7971383) baseStart_7971383 baseEnd_7971383 := by
    simpa [prefixWord, tailWord_7971383, baseEnd_7971383] using wordTrace_append hprefix tailTrace_7971383
  have hstable : (prefixWord ++ tailWord_7971383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971383).length < 2 ^ (prefixWord ++ tailWord_7971383).sum := by decide
  have hdescent : baseEnd_7971383 < baseStart_7971383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971386 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3]
def baseStart_7971386 : Nat := 118140960795 + 7971386 * 2 ^ 59
def prefixEnd_7971386 : Nat := 4983230072969 + 3 ^ 40 * 7971386 * 2
def baseEnd_7971386 : Nat := 4093152500521054149315269

theorem tailTrace_7971386 : CollatzResearch.WordTrace tailWord_7971386 prefixEnd_7971386 4093152500521054149315269 := by
  unfold tailWord_7971386
  simp only [CollatzResearch.WordTrace]
  refine ⟨72685083174759350296743503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193826888466024934124649341 72685083174759350296743503)
  ·
    refine ⟨109027624762139025445115255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72685083174759350296743503 109027624762139025445115255)
    ·
      refine ⟨163541437143208538167672883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109027624762139025445115255 163541437143208538167672883)
      ·
        refine ⟨245312155714812807251509325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163541437143208538167672883 245312155714812807251509325)
        ·
          refine ⟨91992058393054802719315997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245312155714812807251509325 91992058393054802719315997)
          ·
            refine ⟨34497021897395551019743499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91992058393054802719315997 34497021897395551019743499)
            ·
              refine ⟨51745532846093326529615249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34497021897395551019743499 51745532846093326529615249)
              ·
                refine ⟨38809149634569994897211437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51745532846093326529615249 38809149634569994897211437)
                ·
                  refine ⟨14553431112963748086454289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38809149634569994897211437 14553431112963748086454289)
                  ·
                    refine ⟨10915073334722811064840717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14553431112963748086454289 10915073334722811064840717)
                    ·
                      refine ⟨4093152500521054149315269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10915073334722811064840717 4093152500521054149315269)
                      ·
                        rfl

theorem cell23_7971386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_7971386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971386 prefixEnd_7971386 := by exact prefixLift 7971386
  have htrace : WordTrace (prefixWord ++ tailWord_7971386) baseStart_7971386 baseEnd_7971386 := by
    simpa [prefixWord, tailWord_7971386, baseEnd_7971386] using wordTrace_append hprefix tailTrace_7971386
  have hstable : (prefixWord ++ tailWord_7971386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971386).length < 2 ^ (prefixWord ++ tailWord_7971386).sum := by decide
  have hdescent : baseEnd_7971386 < baseStart_7971386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971393 : List Nat := [1, 2, 5, 1, 1, 2, 2, 3, 2, 4]
def baseStart_7971393 : Nat := 118140960795 + 7971393 * 2 ^ 59
def prefixEnd_7971393 : Nat := 4983230072969 + 3 ^ 40 * 7971393 * 2
def baseEnd_7971393 : Nat := 1364385364961878540642579

theorem tailTrace_7971393 : CollatzResearch.WordTrace tailWord_7971393 prefixEnd_7971393 1364385364961878540642579 := by
  unfold tailWord_7971393
  simp only [CollatzResearch.WordTrace]
  refine ⟨290740588010012041382478833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193827058673341360921652555 290740588010012041382478833)
  ·
    refine ⟨218055441007509031036859125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290740588010012041382478833 218055441007509031036859125)
    ·
      refine ⟨20442697594453971659705543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218055441007509031036859125 20442697594453971659705543)
      ·
        refine ⟨30664046391680957489558315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20442697594453971659705543 30664046391680957489558315)
        ·
          refine ⟨45996069587521436234337473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30664046391680957489558315 45996069587521436234337473)
          ·
            refine ⟨34497052190641077175753105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45996069587521436234337473 34497052190641077175753105)
            ·
              refine ⟨25872789142980807881814829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34497052190641077175753105 25872789142980807881814829)
              ·
                refine ⟨9702295928617802955680561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25872789142980807881814829 9702295928617802955680561)
                ·
                  refine ⟨7276721946463352216760421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9702295928617802955680561 7276721946463352216760421)
                  ·
                    refine ⟨1364385364961878540642579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7276721946463352216760421 1364385364961878540642579)
                    ·
                      rfl

theorem cell23_7971393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_7971393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971393 prefixEnd_7971393 := by exact prefixLift 7971393
  have htrace : WordTrace (prefixWord ++ tailWord_7971393) baseStart_7971393 baseEnd_7971393 := by
    simpa [prefixWord, tailWord_7971393, baseEnd_7971393] using wordTrace_append hprefix tailTrace_7971393
  have hstable : (prefixWord ++ tailWord_7971393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971393).length < 2 ^ (prefixWord ++ tailWord_7971393).sum := by decide
  have hdescent : baseEnd_7971393 < baseStart_7971393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971416 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 1, 3, 3]
def baseStart_7971416 : Nat := 118140960795 + 7971416 * 2 ^ 59
def prefixEnd_7971416 : Nat := 4983230072969 + 3 ^ 40 * 7971416 * 2
def baseEnd_7971416 : Nat := 4093167904940689031940131

theorem tailTrace_7971416 : CollatzResearch.WordTrace tailWord_7971416 prefixEnd_7971416 4093167904940689031940131 := by
  unfold tailWord_7971416
  simp only [CollatzResearch.WordTrace]
  refine ⟨145370713444464358155283051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193827617925952477540377401 145370713444464358155283051)
  ·
    refine ⟨218056070166696537232924577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145370713444464358155283051 218056070166696537232924577)
    ·
      refine ⟨163542052625022402924693433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218056070166696537232924577 163542052625022402924693433)
      ·
        refine ⟨122656539468766802193520075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163542052625022402924693433 122656539468766802193520075)
        ·
          refine ⟨183984809203150203290280113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122656539468766802193520075 183984809203150203290280113)
          ·
            refine ⟨137988606902362652467710085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183984809203150203290280113 137988606902362652467710085)
            ·
              refine ⟨25872863794192997337695641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137988606902362652467710085 25872863794192997337695641)
              ·
                refine ⟨19404647845644748003271731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25872863794192997337695641 19404647845644748003271731)
                ·
                  refine ⟨29106971768467122004907597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19404647845644748003271731 29106971768467122004907597)
                  ·
                    refine ⟨10915114413175170751840349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29106971768467122004907597 10915114413175170751840349)
                    ·
                      refine ⟨4093167904940689031940131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10915114413175170751840349 4093167904940689031940131)
                      ·
                        rfl

theorem cell23_7971416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_7971416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971416 prefixEnd_7971416 := by exact prefixLift 7971416
  have htrace : WordTrace (prefixWord ++ tailWord_7971416) baseStart_7971416 baseEnd_7971416 := by
    simpa [prefixWord, tailWord_7971416, baseEnd_7971416] using wordTrace_append hprefix tailTrace_7971416
  have hstable : (prefixWord ++ tailWord_7971416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971416).length < 2 ^ (prefixWord ++ tailWord_7971416).sum := by decide
  have hdescent : baseEnd_7971416 < baseStart_7971416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971420 : List Nat := [2, 2, 4, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_7971420 : Nat := 118140960795 + 7971420 * 2 ^ 59
def prefixEnd_7971420 : Nat := 4983230072969 + 3 ^ 40 * 7971420 * 2
def baseEnd_7971420 : Nat := 4093169958863307016290113

theorem tailTrace_7971420 : CollatzResearch.WordTrace tailWord_7971420 prefixEnd_7971420 4093169958863307016290113 := by
  unfold tailWord_7971420
  simp only [CollatzResearch.WordTrace]
  refine ⟨145370786390457112496855857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193827715187276149995807809 145370786390457112496855857)
  ·
    refine ⟨109028089792842834372641893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145370786390457112496855857 109028089792842834372641893)
    ·
      refine ⟨20442766836158031444870355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109028089792842834372641893 20442766836158031444870355)
      ·
        refine ⟨30664150254237047167305533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20442766836158031444870355 30664150254237047167305533)
        ·
          refine ⟨11499056345338892687739575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30664150254237047167305533 11499056345338892687739575)
          ·
            refine ⟨17248584518008339031609363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11499056345338892687739575 17248584518008339031609363)
            ·
              refine ⟨25872876777012508547414045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17248584518008339031609363 25872876777012508547414045)
              ·
                refine ⟨9702328791379690705280267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25872876777012508547414045 9702328791379690705280267)
                ·
                  refine ⟨14553493187069536057920401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9702328791379690705280267 14553493187069536057920401)
                  ·
                    refine ⟨10915119890302152043440301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14553493187069536057920401 10915119890302152043440301)
                    ·
                      refine ⟨4093169958863307016290113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10915119890302152043440301 4093169958863307016290113)
                      ·
                        rfl

theorem cell23_7971420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_7971420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971420 prefixEnd_7971420 := by exact prefixLift 7971420
  have htrace : WordTrace (prefixWord ++ tailWord_7971420) baseStart_7971420 baseEnd_7971420 := by
    simpa [prefixWord, tailWord_7971420, baseEnd_7971420] using wordTrace_append hprefix tailTrace_7971420
  have hstable : (prefixWord ++ tailWord_7971420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971420).length < 2 ^ (prefixWord ++ tailWord_7971420).sum := by decide
  have hdescent : baseEnd_7971420 < baseStart_7971420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971439 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 4]
def baseStart_7971439 : Nat := 118140960795 + 7971439 * 2 ^ 59
def prefixEnd_7971439 : Nat := 4983230072969 + 3 ^ 40 * 7971439 * 2
def baseEnd_7971439 : Nat := 4093179714995742441952525

theorem tailTrace_7971439 : CollatzResearch.WordTrace tailWord_7971439 prefixEnd_7971439 4093179714995742441952525 := by
  unfold tailWord_7971439
  simp only [CollatzResearch.WordTrace]
  refine ⟨290742265767845391238653371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193828177178563594159102247 290742265767845391238653371)
  ·
    refine ⟨436113398651768086857980057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290742265767845391238653371 436113398651768086857980057)
    ·
      refine ⟨327085048988826065143485043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436113398651768086857980057 327085048988826065143485043)
      ·
        refine ⟨490627573483239097715227565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327085048988826065143485043 490627573483239097715227565)
        ·
          refine ⟨183985340056214661643210337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490627573483239097715227565 183985340056214661643210337)
          ·
            refine ⟨137989005042160996232407753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183985340056214661643210337 137989005042160996232407753)
            ·
              refine ⟨103491753781620747174305815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137989005042160996232407753 103491753781620747174305815)
              ·
                refine ⟨155237630672431120761458723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103491753781620747174305815 155237630672431120761458723)
                ·
                  refine ⟨232856446008646681142188085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155237630672431120761458723 232856446008646681142188085)
                  ·
                    refine ⟨21830291813310626357080133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 232856446008646681142188085 21830291813310626357080133)
                    ·
                      refine ⟨4093179714995742441952525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21830291813310626357080133 4093179714995742441952525)
                      ·
                        rfl

theorem cell23_7971439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_7971439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971439 prefixEnd_7971439 := by exact prefixLift 7971439
  have htrace : WordTrace (prefixWord ++ tailWord_7971439) baseStart_7971439 baseEnd_7971439 := by
    simpa [prefixWord, tailWord_7971439, baseEnd_7971439] using wordTrace_append hprefix tailTrace_7971439
  have hstable : (prefixWord ++ tailWord_7971439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971439).length < 2 ^ (prefixWord ++ tailWord_7971439).sum := by decide
  have hdescent : baseEnd_7971439 < baseStart_7971439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971460 : List Nat := [2, 3, 2, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_7971460 : Nat := 118140960795 + 7971460 * 2 ^ 59
def prefixEnd_7971460 : Nat := 4983230072969 + 3 ^ 40 * 7971460 * 2
def baseEnd_7971460 : Nat := 4093190498089486859789929

theorem tailTrace_7971460 : CollatzResearch.WordTrace tailWord_7971460 prefixEnd_7971460 4093190498089486859789929 := by
  unfold tailWord_7971460
  simp only [CollatzResearch.WordTrace]
  refine ⟨145371515850384655912583917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193828687800512874550111889 145371515850384655912583917)
  ·
    refine ⟨54514318443894245967218969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145371515850384655912583917 54514318443894245967218969)
    ·
      refine ⟨40885738832920684475414227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54514318443894245967218969 40885738832920684475414227)
      ·
        refine ⟨61328608249381026713121341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40885738832920684475414227 61328608249381026713121341)
        ·
          refine ⟨22998228093517885017420503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61328608249381026713121341 22998228093517885017420503)
          ·
            refine ⟨34497342140276827526130755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22998228093517885017420503 34497342140276827526130755)
            ·
              refine ⟨51746013210415241289196133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34497342140276827526130755 51746013210415241289196133)
              ·
                refine ⟨9702377476952857741724275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51746013210415241289196133 9702377476952857741724275)
                ·
                  refine ⟨14553566215429286612586413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9702377476952857741724275 14553566215429286612586413)
                  ·
                    refine ⟨5457587330785982479719905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14553566215429286612586413 5457587330785982479719905)
                    ·
                      refine ⟨4093190498089486859789929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457587330785982479719905 4093190498089486859789929)
                      ·
                        rfl

theorem cell23_7971460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_7971460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971460 prefixEnd_7971460 := by exact prefixLift 7971460
  have htrace : WordTrace (prefixWord ++ tailWord_7971460) baseStart_7971460 baseEnd_7971460 := by
    simpa [prefixWord, tailWord_7971460, baseEnd_7971460] using wordTrace_append hprefix tailTrace_7971460
  have hstable : (prefixWord ++ tailWord_7971460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971460).length < 2 ^ (prefixWord ++ tailWord_7971460).sum := by decide
  have hdescent : baseEnd_7971460 < baseStart_7971460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971506 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_7971506 : Nat := 118140960795 + 7971506 * 2 ^ 59
def prefixEnd_7971506 : Nat := 4983230072969 + 3 ^ 40 * 7971506 * 2
def baseEnd_7971506 : Nat := 4093214118199593679814717

theorem tailTrace_7971506 : CollatzResearch.WordTrace tailWord_7971506 prefixEnd_7971506 4093214118199593679814717 := by
  unfold tailWord_7971506
  simp only [CollatzResearch.WordTrace]
  refine ⟨72686177364650665420335593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193829806305735107787561581 72686177364650665420335593)
  ·
    refine ⟨54514633023487999065251695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72686177364650665420335593 54514633023487999065251695)
    ·
      refine ⟨81771949535231998597877543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54514633023487999065251695 81771949535231998597877543)
      ·
        refine ⟨122657924302847997896816315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81771949535231998597877543 122657924302847997896816315)
        ·
          refine ⟨183986886454271996845224473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122657924302847997896816315 183986886454271996845224473)
          ·
            refine ⟨137990164840703997633918355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183986886454271996845224473 137990164840703997633918355)
            ·
              refine ⟨206985247261055996450877533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137990164840703997633918355 206985247261055996450877533)
              ·
                refine ⟨77619467722895998669079075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206985247261055996450877533 77619467722895998669079075)
                ·
                  refine ⟨116429201584343998003618613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77619467722895998669079075 116429201584343998003618613)
                  ·
                    refine ⟨10915237648532249812839245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116429201584343998003618613 10915237648532249812839245)
                    ·
                      refine ⟨4093214118199593679814717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10915237648532249812839245 4093214118199593679814717)
                      ·
                        rfl

theorem cell23_7971506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_7971506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971506 prefixEnd_7971506 := by exact prefixLift 7971506
  have htrace : WordTrace (prefixWord ++ tailWord_7971506) baseStart_7971506 baseEnd_7971506 := by
    simpa [prefixWord, tailWord_7971506, baseEnd_7971506] using wordTrace_append hprefix tailTrace_7971506
  have hstable : (prefixWord ++ tailWord_7971506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971506).length < 2 ^ (prefixWord ++ tailWord_7971506).sum := by decide
  have hdescent : baseEnd_7971506 < baseStart_7971506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971507 : List Nat := [1, 1, 1, 2, 3, 4, 4, 1, 2, 2, 2]
def baseStart_7971507 : Nat := 118140960795 + 7971507 * 2 ^ 59
def prefixEnd_7971507 : Nat := 4983230072969 + 3 ^ 40 * 7971507 * 2
def baseEnd_7971507 : Nat := 4093214631680248175902213

theorem tailTrace_7971507 : CollatzResearch.WordTrace tailWord_7971507 prefixEnd_7971507 4093214631680248175902213 := by
  unfold tailWord_7971507
  simp only [CollatzResearch.WordTrace]
  refine ⟨290744745931599038852128775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193829830621066025901419183 290744745931599038852128775)
  ·
    refine ⟨436117118897398558278193163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290744745931599038852128775 436117118897398558278193163)
    ·
      refine ⟨654175678346097837417289745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436117118897398558278193163 654175678346097837417289745)
      ·
        refine ⟨490631758759573378062967309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654175678346097837417289745 490631758759573378062967309)
        ·
          refine ⟨183986909534840016773612741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490631758759573378062967309 183986909534840016773612741)
          ·
            refine ⟨34497545537782503145052389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183986909534840016773612741 34497545537782503145052389)
            ·
              refine ⟨6468289788334219339697323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34497545537782503145052389 6468289788334219339697323)
              ·
                refine ⟨9702434682501329009545985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6468289788334219339697323 9702434682501329009545985)
                ·
                  refine ⟨7276826011875996757159489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9702434682501329009545985 7276826011875996757159489)
                  ·
                    refine ⟨5457619508906997567869617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7276826011875996757159489 5457619508906997567869617)
                    ·
                      refine ⟨4093214631680248175902213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457619508906997567869617 4093214631680248175902213)
                      ·
                        rfl

theorem cell23_7971507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 2, 2, 2].length) (baseStart_7971507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971507 prefixEnd_7971507 := by exact prefixLift 7971507
  have htrace : WordTrace (prefixWord ++ tailWord_7971507) baseStart_7971507 baseEnd_7971507 := by
    simpa [prefixWord, tailWord_7971507, baseEnd_7971507] using wordTrace_append hprefix tailTrace_7971507
  have hstable : (prefixWord ++ tailWord_7971507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971507).length < 2 ^ (prefixWord ++ tailWord_7971507).sum := by decide
  have hdescent : baseEnd_7971507 < baseStart_7971507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971580 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_7971580 : Nat := 118140960795 + 7971580 * 2 ^ 59
def prefixEnd_7971580 : Nat := 4983230072969 + 3 ^ 40 * 7971580 * 2
def baseEnd_7971580 : Nat := 4093252115768026390289377

theorem tailTrace_7971580 : CollatzResearch.WordTrace tailWord_7971580 prefixEnd_7971580 4093252115768026390289377 := by
  unfold tailWord_7971580
  simp only [CollatzResearch.WordTrace]
  refine ⟨145373704230167286159768097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193831605640223048213024129 145373704230167286159768097)
  ·
    refine ⟨109030278172625464619826073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145373704230167286159768097 109030278172625464619826073)
    ·
      refine ⟨81772708629469098464869555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109030278172625464619826073 81772708629469098464869555)
      ·
        refine ⟨122659062944203647697304333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81772708629469098464869555 122659062944203647697304333)
        ·
          refine ⟨45997148604076367886489125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122659062944203647697304333 45997148604076367886489125)
          ·
            refine ⟨8624465363264318978716711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45997148604076367886489125 8624465363264318978716711)
            ·
              refine ⟨12936698044896478468075067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8624465363264318978716711 12936698044896478468075067)
              ·
                refine ⟨19405047067344717702112601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12936698044896478468075067 19405047067344717702112601)
                ·
                  refine ⟨14553785300508538276584451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19405047067344717702112601 14553785300508538276584451)
                  ·
                    refine ⟨21830677950762807414876677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14553785300508538276584451 21830677950762807414876677)
                    ·
                      refine ⟨4093252115768026390289377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21830677950762807414876677 4093252115768026390289377)
                      ·
                        rfl

theorem cell23_7971580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_7971580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971580 prefixEnd_7971580 := by exact prefixLift 7971580
  have htrace : WordTrace (prefixWord ++ tailWord_7971580) baseStart_7971580 baseEnd_7971580 := by
    simpa [prefixWord, tailWord_7971580, baseEnd_7971580] using wordTrace_append hprefix tailTrace_7971580
  have hstable : (prefixWord ++ tailWord_7971580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971580).length < 2 ^ (prefixWord ++ tailWord_7971580).sum := by decide
  have hdescent : baseEnd_7971580 < baseStart_7971580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971640 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 2, 3, 2]
def baseStart_7971640 : Nat := 118140960795 + 7971640 * 2 ^ 59
def prefixEnd_7971640 : Nat := 4983230072969 + 3 ^ 40 * 7971640 * 2
def baseEnd_7971640 : Nat := 4093282924607296155539101

theorem tailTrace_7971640 : CollatzResearch.WordTrace tailWord_7971640 prefixEnd_7971640 4093282924607296155539101 := by
  unfold tailWord_7971640
  simp only [CollatzResearch.WordTrace]
  refine ⟨145374798420058601283360187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193833064560078135044480249 145374798420058601283360187)
  ·
    refine ⟨218062197630087901925040281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145374798420058601283360187 218062197630087901925040281)
    ·
      refine ⟨163546648222565926443780211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218062197630087901925040281 163546648222565926443780211)
      ·
        refine ⟨245319972333848889665670317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163546648222565926443780211 245319972333848889665670317)
        ·
          refine ⟨91994989625193333624626369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245319972333848889665670317 91994989625193333624626369)
          ·
            refine ⟨68996242218895000218469777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91994989625193333624626369 68996242218895000218469777)
            ·
              refine ⟨51747181664171250163852333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68996242218895000218469777 51747181664171250163852333)
              ·
                refine ⟨19405193124064218811444625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51747181664171250163852333 19405193124064218811444625)
                ·
                  refine ⟨14553894843048164108583469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19405193124064218811444625 14553894843048164108583469)
                  ·
                    refine ⟨5457710566143061540718801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14553894843048164108583469 5457710566143061540718801)
                    ·
                      refine ⟨4093282924607296155539101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457710566143061540718801 4093282924607296155539101)
                      ·
                        rfl

theorem cell23_7971640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2, 3, 2].length) (baseStart_7971640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971640 prefixEnd_7971640 := by exact prefixLift 7971640
  have htrace : WordTrace (prefixWord ++ tailWord_7971640) baseStart_7971640 baseEnd_7971640 := by
    simpa [prefixWord, tailWord_7971640, baseEnd_7971640] using wordTrace_append hprefix tailTrace_7971640
  have hstable : (prefixWord ++ tailWord_7971640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971640).length < 2 ^ (prefixWord ++ tailWord_7971640).sum := by decide
  have hdescent : baseEnd_7971640 < baseStart_7971640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971673 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 5]
def baseStart_7971673 : Nat := 118140960795 + 7971673 * 2 ^ 59
def prefixEnd_7971673 : Nat := 4983230072969 + 3 ^ 40 * 7971673 * 2
def baseEnd_7971673 : Nat := 4093299869468894526426449

theorem tailTrace_7971673 : CollatzResearch.WordTrace tailWord_7971673 prefixEnd_7971673 4093299869468894526426449 := by
  unfold tailWord_7971673
  simp only [CollatzResearch.WordTrace]
  refine ⟨290750800448997649202671673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193833866965998432801781115 290750800448997649202671673)
  ·
    refine ⟨218063100336748236902003755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290750800448997649202671673 218063100336748236902003755)
    ·
      refine ⟨327094650505122355353005633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218063100336748236902003755 327094650505122355353005633)
      ·
        refine ⟨245320987878841766514754225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327094650505122355353005633 245320987878841766514754225)
        ·
          refine ⟨183990740909131324886065669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245320987878841766514754225 183990740909131324886065669)
          ·
            refine ⟨34498263920462123416137313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183990740909131324886065669 34498263920462123416137313)
            ·
              refine ⟨25873697940346592562102985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34498263920462123416137313 25873697940346592562102985)
              ·
                refine ⟨19405273455259944421577239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25873697940346592562102985 19405273455259944421577239)
                ·
                  refine ⟨29107910182889916632365859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19405273455259944421577239 29107910182889916632365859)
                  ·
                    refine ⟨43661865274334874948548789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29107910182889916632365859 43661865274334874948548789)
                    ·
                      refine ⟨4093299869468894526426449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43661865274334874948548789 4093299869468894526426449)
                      ·
                        rfl

theorem cell23_7971673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_7971673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971673 prefixEnd_7971673 := by exact prefixLift 7971673
  have htrace : WordTrace (prefixWord ++ tailWord_7971673) baseStart_7971673 baseEnd_7971673 := by
    simpa [prefixWord, tailWord_7971673, baseEnd_7971673] using wordTrace_append hprefix tailTrace_7971673
  have hstable : (prefixWord ++ tailWord_7971673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971673).length < 2 ^ (prefixWord ++ tailWord_7971673).sum := by decide
  have hdescent : baseEnd_7971673 < baseStart_7971673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971680 : List Nat := [2, 1, 1, 3, 3, 1, 3, 3, 2, 4]
def baseStart_7971680 : Nat := 118140960795 + 7971680 * 2 ^ 59
def prefixEnd_7971680 : Nat := 4983230072969 + 3 ^ 40 * 7971680 * 2
def baseEnd_7971680 : Nat := 1364434487944491999679639

theorem tailTrace_7971680 : CollatzResearch.WordTrace tailWord_7971680 prefixEnd_7971680 1364434487944491999679639 := by
  unfold tailWord_7971680
  simp only [CollatzResearch.WordTrace]
  refine ⟨145375527879986144699088247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193834037173314859598784329 145375527879986144699088247)
  ·
    refine ⟨218063291819979217048632371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145375527879986144699088247 218063291819979217048632371)
    ·
      refine ⟨327094937729968825572948557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218063291819979217048632371 327094937729968825572948557)
      ·
        refine ⟨122660601648738309589855709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327094937729968825572948557 122660601648738309589855709)
        ·
          refine ⟨45997725618276866096195891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122660601648738309589855709 45997725618276866096195891)
          ·
            refine ⟨68996588427415299144293837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45997725618276866096195891 68996588427415299144293837)
            ·
              refine ⟨25873720660280737179110189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68996588427415299144293837 25873720660280737179110189)
              ·
                refine ⟨9702645247605276442166321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25873720660280737179110189 9702645247605276442166321)
                ·
                  refine ⟨7276983935703957331624741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9702645247605276442166321 7276983935703957331624741)
                  ·
                    refine ⟨1364434487944491999679639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7276983935703957331624741 1364434487944491999679639)
                    ·
                      rfl

theorem cell23_7971680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 2, 4].length) (baseStart_7971680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971680 prefixEnd_7971680 := by exact prefixLift 7971680
  have htrace : WordTrace (prefixWord ++ tailWord_7971680) baseStart_7971680 baseEnd_7971680 := by
    simpa [prefixWord, tailWord_7971680, baseEnd_7971680] using wordTrace_append hprefix tailTrace_7971680
  have hstable : (prefixWord ++ tailWord_7971680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971680).length < 2 ^ (prefixWord ++ tailWord_7971680).sum := by decide
  have hdescent : baseEnd_7971680 < baseStart_7971680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971683 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 6]
def baseStart_7971683 : Nat := 118140960795 + 7971683 * 2 ^ 59
def prefixEnd_7971683 : Nat := 4983230072969 + 3 ^ 40 * 7971683 * 2
def baseEnd_7971683 : Nat := 4093305004275439487301403

theorem tailTrace_7971683 : CollatzResearch.WordTrace tailWord_7971683 prefixEnd_7971683 4093305004275439487301403 := by
  unfold tailWord_7971683
  simp only [CollatzResearch.WordTrace]
  refine ⟨290751165178961420910535703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193834110119307613940357135 290751165178961420910535703)
  ·
    refine ⟨436126747768442131365803555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290751165178961420910535703 436126747768442131365803555)
    ·
      refine ⟨654190121652663197048705333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436126747768442131365803555 654190121652663197048705333)
      ·
        refine ⟨61330323904937174723316125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 654190121652663197048705333 61330323904937174723316125)
        ·
          refine ⟨22998871464351440521243547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61330323904937174723316125 22998871464351440521243547)
          ·
            refine ⟨34498307196527160781865321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22998871464351440521243547 34498307196527160781865321)
            ·
              refine ⟨25873730397395370586398991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34498307196527160781865321 25873730397395370586398991)
              ·
                refine ⟨38810595596093055879598487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25873730397395370586398991 38810595596093055879598487)
                ·
                  refine ⟨58215893394139583819397731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38810595596093055879598487 58215893394139583819397731)
                  ·
                    refine ⟨87323840091209375729096597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58215893394139583819397731 87323840091209375729096597)
                    ·
                      refine ⟨4093305004275439487301403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87323840091209375729096597 4093305004275439487301403)
                      ·
                        rfl

theorem cell23_7971683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_7971683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971683 prefixEnd_7971683 := by exact prefixLift 7971683
  have htrace : WordTrace (prefixWord ++ tailWord_7971683) baseStart_7971683 baseEnd_7971683 := by
    simpa [prefixWord, tailWord_7971683, baseEnd_7971683] using wordTrace_append hprefix tailTrace_7971683
  have hstable : (prefixWord ++ tailWord_7971683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971683).length < 2 ^ (prefixWord ++ tailWord_7971683).sum := by decide
  have hdescent : baseEnd_7971683 < baseStart_7971683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971687 : List Nat := [1, 1, 5, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_7971687 : Nat := 118140960795 + 7971687 * 2 ^ 59
def prefixEnd_7971687 : Nat := 4983230072969 + 3 ^ 40 * 7971687 * 2
def baseEnd_7971687 : Nat := 4093307058198057471651385

theorem tailTrace_7971687 : CollatzResearch.WordTrace tailWord_7971687 prefixEnd_7971687 4093307058198057471651385 := by
  unfold tailWord_7971687
  simp only [CollatzResearch.WordTrace]
  refine ⟨290751311070946929593681315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193834207380631286395787543 290751311070946929593681315)
  ·
    refine ⟨436126966606420394390521973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290751311070946929593681315 436126966606420394390521973)
    ·
      refine ⟨40886903119351911974111435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 436126966606420394390521973 40886903119351911974111435)
      ·
        refine ⟨61330354679027867961167153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40886903119351911974111435 61330354679027867961167153)
        ·
          refine ⟨45997766009270900970875365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61330354679027867961167153 45997766009270900970875365)
          ·
            refine ⟨8624581126738293932039131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45997766009270900970875365 8624581126738293932039131)
            ·
              refine ⟨12936871690107440898058697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8624581126738293932039131 12936871690107440898058697)
              ·
                refine ⟨9702653767580580673544023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12936871690107440898058697 9702653767580580673544023)
                ·
                  refine ⟨14553980651370871010316035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9702653767580580673544023 14553980651370871010316035)
                  ·
                    refine ⟨21830970977056306515474053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14553980651370871010316035 21830970977056306515474053)
                    ·
                      refine ⟨4093307058198057471651385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21830970977056306515474053 4093307058198057471651385)
                      ·
                        rfl

theorem cell23_7971687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_7971687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971687 prefixEnd_7971687 := by exact prefixLift 7971687
  have htrace : WordTrace (prefixWord ++ tailWord_7971687) baseStart_7971687 baseEnd_7971687 := by
    simpa [prefixWord, tailWord_7971687, baseEnd_7971687] using wordTrace_append hprefix tailTrace_7971687
  have hstable : (prefixWord ++ tailWord_7971687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971687).length < 2 ^ (prefixWord ++ tailWord_7971687).sum := by decide
  have hdescent : baseEnd_7971687 < baseStart_7971687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971710 : List Nat := [4, 2, 3, 1, 2, 11]
def baseStart_7971710 : Nat := 118140960795 + 7971710 * 2 ^ 59
def prefixEnd_7971710 : Nat := 4983230072969 + 3 ^ 40 * 7971710 * 2
def baseEnd_7971710 : Nat := 16844933614210332846353

theorem tailTrace_7971710 : CollatzResearch.WordTrace tailWord_7971710 prefixEnd_7971710 16844933614210332846353 := by
  unfold tailWord_7971710
  simp only [CollatzResearch.WordTrace]
  refine ⟨36344018743732950565221073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193834766633242403014512389 36344018743732950565221073)
  ·
    refine ⟨27258014057799712923915805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36344018743732950565221073 27258014057799712923915805)
    ·
      refine ⟨10221755271674892346468427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27258014057799712923915805 10221755271674892346468427)
      ·
        refine ⟨15332632907512338519702641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10221755271674892346468427 15332632907512338519702641)
        ·
          refine ⟨11499474680634253889776981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15332632907512338519702641 11499474680634253889776981)
          ·
            refine ⟨16844933614210332846353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11499474680634253889776981 16844933614210332846353)
            ·
              rfl

theorem cell23_7971710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 11].length) (baseStart_7971710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971710 prefixEnd_7971710 := by exact prefixLift 7971710
  have htrace : WordTrace (prefixWord ++ tailWord_7971710) baseStart_7971710 baseEnd_7971710 := by
    simpa [prefixWord, tailWord_7971710, baseEnd_7971710] using wordTrace_append hprefix tailTrace_7971710
  have hstable : (prefixWord ++ tailWord_7971710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971710).length < 2 ^ (prefixWord ++ tailWord_7971710).sum := by decide
  have hdescent : baseEnd_7971710 < baseStart_7971710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971721 : List Nat := [1, 2, 1, 1, 5, 2, 4, 2, 1, 2, 2]
def baseStart_7971721 : Nat := 118140960795 + 7971721 * 2 ^ 59
def prefixEnd_7971721 : Nat := 4983230072969 + 3 ^ 40 * 7971721 * 2
def baseEnd_7971721 : Nat := 4093324516540310338626229

theorem tailTrace_7971721 : CollatzResearch.WordTrace tailWord_7971721 prefixEnd_7971721 4093324516540310338626229 := by
  unfold tailWord_7971721
  simp only [CollatzResearch.WordTrace]
  refine ⟨290752551152823753400419017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193835034101882502266946011 290752551152823753400419017)
  ·
    refine ⟨218064413364617815050314263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290752551152823753400419017 218064413364617815050314263)
    ·
      refine ⟨327096620046926722575471395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218064413364617815050314263 327096620046926722575471395)
      ·
        refine ⟨490644930070390083863207093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327096620046926722575471395 490644930070390083863207093)
        ·
          refine ⟨45997962194099070362175665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 490644930070390083863207093 45997962194099070362175665)
          ·
            refine ⟨34498471645574302771631749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45997962194099070362175665 34498471645574302771631749)
            ·
              refine ⟨6468463433545181769680953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34498471645574302771631749 6468463433545181769680953)
              ·
                refine ⟨4851347575158886327260715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6468463433545181769680953 4851347575158886327260715)
                ·
                  refine ⟨7277021362738329490891073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4851347575158886327260715 7277021362738329490891073)
                  ·
                    refine ⟨5457766022053747118168305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7277021362738329490891073 5457766022053747118168305)
                    ·
                      refine ⟨4093324516540310338626229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457766022053747118168305 4093324516540310338626229)
                      ·
                        rfl

theorem cell23_7971721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 1, 2, 2].length) (baseStart_7971721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971721 prefixEnd_7971721 := by exact prefixLift 7971721
  have htrace : WordTrace (prefixWord ++ tailWord_7971721) baseStart_7971721 baseEnd_7971721 := by
    simpa [prefixWord, tailWord_7971721, baseEnd_7971721] using wordTrace_append hprefix tailTrace_7971721
  have hstable : (prefixWord ++ tailWord_7971721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971721).length < 2 ^ (prefixWord ++ tailWord_7971721).sum := by decide
  have hdescent : baseEnd_7971721 < baseStart_7971721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971734 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_7971734 : Nat := 118140960795 + 7971734 * 2 ^ 59
def prefixEnd_7971734 : Nat := 4983230072969 + 3 ^ 40 * 7971734 * 2
def baseEnd_7971734 : Nat := 4093331191788818787763669

theorem tailTrace_7971734 : CollatzResearch.WordTrace tailWord_7971734 prefixEnd_7971734 4093331191788818787763669 := by
  unfold tailWord_7971734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18172064081361041038790141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193835350201184437747094837 18172064081361041038790141)
  ·
    refine ⟨6814524030510390389546303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18172064081361041038790141 6814524030510390389546303)
    ·
      refine ⟨10221786045765585584319455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6814524030510390389546303 10221786045765585584319455)
      ·
        refine ⟨15332679068648378376479183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10221786045765585584319455 15332679068648378376479183)
        ·
          refine ⟨22999018602972567564718775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15332679068648378376479183 22999018602972567564718775)
          ·
            refine ⟨34498527904458851347078163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22999018602972567564718775 34498527904458851347078163)
            ·
              refine ⟨51747791856688277020617245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34498527904458851347078163 51747791856688277020617245)
              ·
                refine ⟨19405421946258103882731467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51747791856688277020617245 19405421946258103882731467)
                ·
                  refine ⟨29108132919387155824097201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19405421946258103882731467 29108132919387155824097201)
                  ·
                    refine ⟨21831099689540366868072901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29108132919387155824097201 21831099689540366868072901)
                    ·
                      refine ⟨4093331191788818787763669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21831099689540366868072901 4093331191788818787763669)
                      ·
                        rfl

theorem cell23_7971734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_7971734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971734 prefixEnd_7971734 := by exact prefixLift 7971734
  have htrace : WordTrace (prefixWord ++ tailWord_7971734) baseStart_7971734 baseEnd_7971734 := by
    simpa [prefixWord, tailWord_7971734, baseEnd_7971734] using wordTrace_append hprefix tailTrace_7971734
  have hstable : (prefixWord ++ tailWord_7971734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971734).length < 2 ^ (prefixWord ++ tailWord_7971734).sum := by decide
  have hdescent : baseEnd_7971734 < baseStart_7971734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971763 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 3]
def baseStart_7971763 : Nat := 118140960795 + 7971763 * 2 ^ 59
def prefixEnd_7971763 : Nat := 4983230072969 + 3 ^ 40 * 7971763 * 2
def baseEnd_7971763 : Nat := 4093346082727799174301035

theorem tailTrace_7971763 : CollatzResearch.WordTrace tailWord_7971763 prefixEnd_7971763 4093346082727799174301035 := by
  unfold tailWord_7971763
  simp only [CollatzResearch.WordTrace]
  refine ⟨290754083018671594573447943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193836055345781063048965295 290754083018671594573447943)
  ·
    refine ⟨436131124528007391860171915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290754083018671594573447943 436131124528007391860171915)
    ·
      refine ⟨654196686792011087790257873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436131124528007391860171915 654196686792011087790257873)
      ·
        refine ⟨490647515094008315842693405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654196686792011087790257873 490647515094008315842693405)
        ·
          refine ⟨183992818160253118441010027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490647515094008315842693405 183992818160253118441010027)
          ·
            refine ⟨275989227240379677661515041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183992818160253118441010027 275989227240379677661515041)
            ·
              refine ⟨206991920430284758246136281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275989227240379677661515041 206991920430284758246136281)
              ·
                refine ⟨155243940322713568684602211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206991920430284758246136281 155243940322713568684602211)
                ·
                  refine ⟨232865910484070353026903317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155243940322713568684602211 232865910484070353026903317)
                  ·
                    refine ⟨10915589553940797798136093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 232865910484070353026903317 10915589553940797798136093)
                    ·
                      refine ⟨4093346082727799174301035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10915589553940797798136093 4093346082727799174301035)
                      ·
                        rfl

theorem cell23_7971763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 3].length) (baseStart_7971763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971763 prefixEnd_7971763 := by exact prefixLift 7971763
  have htrace : WordTrace (prefixWord ++ tailWord_7971763) baseStart_7971763 baseEnd_7971763 := by
    simpa [prefixWord, tailWord_7971763, baseEnd_7971763] using wordTrace_append hprefix tailTrace_7971763
  have hstable : (prefixWord ++ tailWord_7971763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971763).length < 2 ^ (prefixWord ++ tailWord_7971763).sum := by decide
  have hdescent : baseEnd_7971763 < baseStart_7971763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971783 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 7]
def baseStart_7971783 : Nat := 118140960795 + 7971783 * 2 ^ 59
def prefixEnd_7971783 : Nat := 4983230072969 + 3 ^ 40 * 7971783 * 2
def baseEnd_7971783 : Nat := 454817372482321010672327

theorem tailTrace_7971783 : CollatzResearch.WordTrace tailWord_7971783 prefixEnd_7971783 454817372482321010672327 := by
  unfold tailWord_7971783
  simp only [CollatzResearch.WordTrace]
  refine ⟨290754812478599137989176003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193836541652399425326117335 290754812478599137989176003)
  ·
    refine ⟨436132218717898706983764005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290754812478599137989176003 436132218717898706983764005)
    ·
      refine ⟨81774791009606007559455751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 436132218717898706983764005 81774791009606007559455751)
      ·
        refine ⟨122662186514409011339183627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81774791009606007559455751 122662186514409011339183627)
        ·
          refine ⟨183993279771613517008775441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122662186514409011339183627 183993279771613517008775441)
          ·
            refine ⟨137994959828710137756581581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183993279771613517008775441 137994959828710137756581581)
            ·
              refine ⟨51748109935766301658718093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137994959828710137756581581 51748109935766301658718093)
              ·
                refine ⟨19405541225912363122019285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51748109935766301658718093 19405541225912363122019285)
                ·
                  refine ⟨454817372482321010672327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19405541225912363122019285 454817372482321010672327)
                  ·
                    rfl

theorem cell23_7971783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 7].length) (baseStart_7971783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971783 prefixEnd_7971783 := by exact prefixLift 7971783
  have htrace : WordTrace (prefixWord ++ tailWord_7971783) baseStart_7971783 baseEnd_7971783 := by
    simpa [prefixWord, tailWord_7971783, baseEnd_7971783] using wordTrace_append hprefix tailTrace_7971783
  have hstable : (prefixWord ++ tailWord_7971783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971783).length < 2 ^ (prefixWord ++ tailWord_7971783).sum := by decide
  have hdescent : baseEnd_7971783 < baseStart_7971783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971790 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_7971790 : Nat := 118140960795 + 7971790 * 2 ^ 59
def prefixEnd_7971790 : Nat := 4983230072969 + 3 ^ 40 * 7971790 * 2
def baseEnd_7971790 : Nat := 4093359946705470568663411

theorem tailTrace_7971790 : CollatzResearch.WordTrace tailWord_7971790 prefixEnd_7971790 4093359946705470568663411 := by
  unfold tailWord_7971790
  simp only [CollatzResearch.WordTrace]
  refine ⟨36344383473696722273085103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193836711859715852123120549 36344383473696722273085103)
  ·
    refine ⟨54516575210545083409627655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36344383473696722273085103 54516575210545083409627655)
    ·
      refine ⟨81774862815817625114441483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54516575210545083409627655 81774862815817625114441483)
      ·
        refine ⟨122662294223726437671662225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81774862815817625114441483 122662294223726437671662225)
        ·
          refine ⟨91996720667794828253746669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122662294223726437671662225 91996720667794828253746669)
          ·
            refine ⟨34498770250423060595155001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91996720667794828253746669 34498770250423060595155001)
            ·
              refine ⟨25874077687817295446366251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34498770250423060595155001 25874077687817295446366251)
              ·
                refine ⟨38811116531725943169549377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25874077687817295446366251 38811116531725943169549377)
                ·
                  refine ⟨29108337398794457377162033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38811116531725943169549377 29108337398794457377162033)
                  ·
                    refine ⟨21831253049095843032871525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29108337398794457377162033 21831253049095843032871525)
                    ·
                      refine ⟨4093359946705470568663411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21831253049095843032871525 4093359946705470568663411)
                      ·
                        rfl

theorem cell23_7971790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_7971790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971790 prefixEnd_7971790 := by exact prefixLift 7971790
  have htrace : WordTrace (prefixWord ++ tailWord_7971790) baseStart_7971790 baseEnd_7971790 := by
    simpa [prefixWord, tailWord_7971790, baseEnd_7971790] using wordTrace_append hprefix tailTrace_7971790
  have hstable : (prefixWord ++ tailWord_7971790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971790).length < 2 ^ (prefixWord ++ tailWord_7971790).sum := by decide
  have hdescent : baseEnd_7971790 < baseStart_7971790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971794 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_7971794 : Nat := 118140960795 + 7971794 * 2 ^ 59
def prefixEnd_7971794 : Nat := 4983230072969 + 3 ^ 40 * 7971794 * 2
def baseEnd_7971794 : Nat := 4093362000628088553013393

theorem tailTrace_7971794 : CollatzResearch.WordTrace tailWord_7971794 prefixEnd_7971794 4093362000628088553013393 := by
  unfold tailWord_7971794
  simp only [CollatzResearch.WordTrace]
  refine ⟨72688803420389821716956609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193836809121039524578550957 72688803420389821716956609)
  ·
    refine ⟨54516602565292366287717457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72688803420389821716956609 54516602565292366287717457)
    ·
      refine ⟨40887451923969274715788093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54516602565292366287717457 40887451923969274715788093)
      ·
        refine ⟨15332794471488478018420535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40887451923969274715788093 15332794471488478018420535)
        ·
          refine ⟨22999191707232717027630803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15332794471488478018420535 22999191707232717027630803)
          ·
            refine ⟨34498787560849075541446205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22999191707232717027630803 34498787560849075541446205)
            ·
              refine ⟨12937045335318403328042327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34498787560849075541446205 12937045335318403328042327)
              ·
                refine ⟨19405568002977604992063491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12937045335318403328042327 19405568002977604992063491)
                ·
                  refine ⟨29108352004466407488095237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19405568002977604992063491 29108352004466407488095237)
                  ·
                    refine ⟨5457816000837451404017857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29108352004466407488095237 5457816000837451404017857)
                    ·
                      refine ⟨4093362000628088553013393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457816000837451404017857 4093362000628088553013393)
                      ·
                        rfl

theorem cell23_7971794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_7971794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971794 prefixEnd_7971794 := by exact prefixLift 7971794
  have htrace : WordTrace (prefixWord ++ tailWord_7971794) baseStart_7971794 baseEnd_7971794 := by
    simpa [prefixWord, tailWord_7971794, baseEnd_7971794] using wordTrace_append hprefix tailTrace_7971794
  have hstable : (prefixWord ++ tailWord_7971794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971794).length < 2 ^ (prefixWord ++ tailWord_7971794).sum := by decide
  have hdescent : baseEnd_7971794 < baseStart_7971794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971820 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 3, 7, 2]
def baseStart_7971820 : Nat := 118140960795 + 7971820 * 2 ^ 59
def prefixEnd_7971820 : Nat := 4983230072969 + 3 ^ 40 * 7971820 * 2
def baseEnd_7971820 : Nat := 4093375351125105451288273

theorem tailTrace_7971820 : CollatzResearch.WordTrace tailWord_7971820 prefixEnd_7971820 4093375351125105451288273 := by
  unfold tailWord_7971820
  simp only [CollatzResearch.WordTrace]
  refine ⟨145378080989732546654136457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193837441319643395538848609 145378080989732546654136457)
  ·
    refine ⟨109033560742299409990602343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145378080989732546654136457 109033560742299409990602343)
    ·
      refine ⟨163550341113449114985903515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109033560742299409990602343 163550341113449114985903515)
      ·
        refine ⟨245325511670173672478855273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163550341113449114985903515 245325511670173672478855273)
        ·
          refine ⟨183994133752630254359141455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245325511670173672478855273 183994133752630254359141455)
          ·
            refine ⟨275991200628945381538712183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183994133752630254359141455 275991200628945381538712183)
            ·
              refine ⟨413986800943418072308068275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275991200628945381538712183 413986800943418072308068275)
              ·
                refine ⟨620980201415127108462102413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413986800943418072308068275 620980201415127108462102413)
                ·
                  refine ⟨232867575530672665673288405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620980201415127108462102413 232867575530672665673288405)
                  ·
                    refine ⟨5457833801500140601717697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 232867575530672665673288405 5457833801500140601717697)
                    ·
                      refine ⟨4093375351125105451288273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5457833801500140601717697 4093375351125105451288273)
                      ·
                        rfl

theorem cell23_7971820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 7, 2].length) (baseStart_7971820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971820 prefixEnd_7971820 := by exact prefixLift 7971820
  have htrace : WordTrace (prefixWord ++ tailWord_7971820) baseStart_7971820 baseEnd_7971820 := by
    simpa [prefixWord, tailWord_7971820, baseEnd_7971820] using wordTrace_append hprefix tailTrace_7971820
  have hstable : (prefixWord ++ tailWord_7971820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971820).length < 2 ^ (prefixWord ++ tailWord_7971820).sum := by decide
  have hdescent : baseEnd_7971820 < baseStart_7971820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971960 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_7971960 : Nat := 118140960795 + 7971960 * 2 ^ 59
def prefixEnd_7971960 : Nat := 4983230072969 + 3 ^ 40 * 7971960 * 2
def baseEnd_7971960 : Nat := 4093447238416734903537629

theorem tailTrace_7971960 : CollatzResearch.WordTrace tailWord_7971960 prefixEnd_7971960 4093447238416734903537629 := by
  unfold tailWord_7971960
  simp only [CollatzResearch.WordTrace]
  refine ⟨145380634099478948609184667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193840845465971931478912889 145380634099478948609184667)
  ·
    refine ⟨218070951149218422913777001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145380634099478948609184667 218070951149218422913777001)
    ·
      refine ⟨163553213361913817185332751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218070951149218422913777001 163553213361913817185332751)
      ·
        refine ⟨245329820042870725777999127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163553213361913817185332751 245329820042870725777999127)
        ·
          refine ⟨367994730064306088666998691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245329820042870725777999127 367994730064306088666998691)
          ·
            refine ⟨551992095096459133000498037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367994730064306088666998691 551992095096459133000498037)
            ·
              refine ⟨51749258915293043718796691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 551992095096459133000498037 51749258915293043718796691)
              ·
                refine ⟨77623888372939565578195037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51749258915293043718796691 77623888372939565578195037)
                ·
                  refine ⟨29108958139852337091823139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77623888372939565578195037 29108958139852337091823139)
                  ·
                    refine ⟨43663437209778505637734709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29108958139852337091823139 43663437209778505637734709)
                    ·
                      refine ⟨4093447238416734903537629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43663437209778505637734709 4093447238416734903537629)
                      ·
                        rfl

theorem cell23_7971960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_7971960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971960 prefixEnd_7971960 := by exact prefixLift 7971960
  have htrace : WordTrace (prefixWord ++ tailWord_7971960) baseStart_7971960 baseEnd_7971960 := by
    simpa [prefixWord, tailWord_7971960, baseEnd_7971960] using wordTrace_append hprefix tailTrace_7971960
  have hstable : (prefixWord ++ tailWord_7971960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971960).length < 2 ^ (prefixWord ++ tailWord_7971960).sum := by decide
  have hdescent : baseEnd_7971960 < baseStart_7971960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7971994 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5]
def baseStart_7971994 : Nat := 118140960795 + 7971994 * 2 ^ 59
def prefixEnd_7971994 : Nat := 4983230072969 + 3 ^ 40 * 7971994 * 2
def baseEnd_7971994 : Nat := 4093464696758987770512473

theorem tailTrace_7971994 : CollatzResearch.WordTrace tailWord_7971994 prefixEnd_7971994 4093464696758987770512473 := by
  unfold tailWord_7971994
  simp only [CollatzResearch.WordTrace]
  refine ⟨72690627070208680256276759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193841672187223147350071357 72690627070208680256276759)
  ·
    refine ⟨109035940605313020384415139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72690627070208680256276759 109035940605313020384415139)
    ·
      refine ⟨163553910907969530576622709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109035940605313020384415139 163553910907969530576622709)
      ·
        refine ⟨15333179147622143491558379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163553910907969530576622709 15333179147622143491558379)
        ·
          refine ⟨22999768721433215237337569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15333179147622143491558379 22999768721433215237337569)
          ·
            refine ⟨17249826541074911428003177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22999768721433215237337569 17249826541074911428003177)
            ·
              refine ⟨12937369905806183571002383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17249826541074911428003177 12937369905806183571002383)
              ·
                refine ⟨19406054858709275356503575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12937369905806183571002383 19406054858709275356503575)
                ·
                  refine ⟨29109082288063913034755363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19406054858709275356503575 29109082288063913034755363)
                  ·
                    refine ⟨43663623432095869552133045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29109082288063913034755363 43663623432095869552133045)
                    ·
                      refine ⟨4093464696758987770512473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43663623432095869552133045 4093464696758987770512473)
                      ·
                        rfl

theorem cell23_7971994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_7971994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7971994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7971994 prefixEnd_7971994 := by exact prefixLift 7971994
  have htrace : WordTrace (prefixWord ++ tailWord_7971994) baseStart_7971994 baseEnd_7971994 := by
    simpa [prefixWord, tailWord_7971994, baseEnd_7971994] using wordTrace_append hprefix tailTrace_7971994
  have hstable : (prefixWord ++ tailWord_7971994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7971994).length < 2 ^ (prefixWord ++ tailWord_7971994).sum := by decide
  have hdescent : baseEnd_7971994 < baseStart_7971994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7971994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972045 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7972045 : Nat := 118140960795 + 7972045 * 2 ^ 59
def prefixEnd_7972045 : Nat := 4983230072969 + 3 ^ 40 * 7972045 * 2
def baseEnd_7972045 : Nat := 4093490884272367070974739

theorem tailTrace_7972045 : CollatzResearch.WordTrace tailWord_7972045 prefixEnd_7972045 4093490884272367070974739 := by
  unfold tailWord_7972045
  simp only [CollatzResearch.WordTrace]
  refine ⟨290764368403649956735213589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193842912269099971156809059 290764368403649956735213589)
  ·
    refine ⟨13629579768921091721963137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 290764368403649956735213589 13629579768921091721963137)
    ·
      refine ⟨10222184826690818791472353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13629579768921091721963137 10222184826690818791472353)
      ·
        refine ⟨7666638620018114093604265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10222184826690818791472353 7666638620018114093604265)
        ·
          refine ⟨5749978965013585570203199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7666638620018114093604265 5749978965013585570203199)
          ·
            refine ⟨8624968447520378355304799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5749978965013585570203199 8624968447520378355304799)
            ·
              refine ⟨12937452671280567532957199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8624968447520378355304799 12937452671280567532957199)
              ·
                refine ⟨19406179006920851299435799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12937452671280567532957199 19406179006920851299435799)
                ·
                  refine ⟨29109268510381276949153699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19406179006920851299435799 29109268510381276949153699)
                  ·
                    refine ⟨43663902765571915423730549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29109268510381276949153699 43663902765571915423730549)
                    ·
                      refine ⟨4093490884272367070974739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43663902765571915423730549 4093490884272367070974739)
                      ·
                        rfl

theorem cell23_7972045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7972045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972045 prefixEnd_7972045 := by exact prefixLift 7972045
  have htrace : WordTrace (prefixWord ++ tailWord_7972045) baseStart_7972045 baseEnd_7972045 := by
    simpa [prefixWord, tailWord_7972045, baseEnd_7972045] using wordTrace_append hprefix tailTrace_7972045
  have hstable : (prefixWord ++ tailWord_7972045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972045).length < 2 ^ (prefixWord ++ tailWord_7972045).sum := by decide
  have hdescent : baseEnd_7972045 < baseStart_7972045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972117 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 4, 5]
def baseStart_7972117 : Nat := 118140960795 + 7972117 * 2 ^ 59
def prefixEnd_7972117 : Nat := 4983230072969 + 3 ^ 40 * 7972117 * 2
def baseEnd_7972117 : Nat := 1364509284959830263091469

theorem tailTrace_7972117 : CollatzResearch.WordTrace tailWord_7972117 prefixEnd_7972117 1364509284959830263091469 := by
  unfold tailWord_7972117
  simp only [CollatzResearch.WordTrace]
  refine ⟨290766994459389113031834605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193844662972926075354556403 290766994459389113031834605)
  ·
    refine ⟨109037622922270917386937977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290766994459389113031834605 109037622922270917386937977)
    ·
      refine ⟨81778217191703188040203483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109037622922270917386937977 81778217191703188040203483)
      ·
        refine ⟨122667325787554782060305225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81778217191703188040203483 122667325787554782060305225)
        ·
          refine ⟨92000494340666086545228919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122667325787554782060305225 92000494340666086545228919)
          ·
            refine ⟨138000741510999129817843379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92000494340666086545228919 138000741510999129817843379)
            ·
              refine ⟨207001112266498694726765069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138000741510999129817843379 207001112266498694726765069)
              ·
                refine ⟨77625417099937010522536901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207001112266498694726765069 77625417099937010522536901)
                ·
                  refine ⟨14554765706238189472975669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77625417099937010522536901 14554765706238189472975669)
                  ·
                    refine ⟨1364509284959830263091469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14554765706238189472975669 1364509284959830263091469)
                    ·
                      rfl

theorem cell23_7972117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_7972117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972117 prefixEnd_7972117 := by exact prefixLift 7972117
  have htrace : WordTrace (prefixWord ++ tailWord_7972117) baseStart_7972117 baseEnd_7972117 := by
    simpa [prefixWord, tailWord_7972117, baseEnd_7972117] using wordTrace_append hprefix tailTrace_7972117
  have hstable : (prefixWord ++ tailWord_7972117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972117).length < 2 ^ (prefixWord ++ tailWord_7972117).sum := by decide
  have hdescent : baseEnd_7972117 < baseStart_7972117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972124 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_7972124 : Nat := 118140960795 + 7972124 * 2 ^ 59
def prefixEnd_7972124 : Nat := 4983230072969 + 3 ^ 40 * 7972124 * 2
def baseEnd_7972124 : Nat := 4093531449244072261886875

theorem tailTrace_7972124 : CollatzResearch.WordTrace tailWord_7972124 prefixEnd_7972124 4093531449244072261886875 := by
  unfold tailWord_7972124
  simp only [CollatzResearch.WordTrace]
  refine ⟨145383624885181876613669713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193844833180242502151559617 145383624885181876613669713)
  ·
    refine ⟨109037718663886407460252285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145383624885181876613669713 109037718663886407460252285)
    ·
      refine ⟨40889144498957402797594607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109037718663886407460252285 40889144498957402797594607)
      ·
        refine ⟨61333716748436104196391911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40889144498957402797594607 61333716748436104196391911)
        ·
          refine ⟨92000575122654156294587867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61333716748436104196391911 92000575122654156294587867)
          ·
            refine ⟨138000862683981234441881801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92000575122654156294587867 138000862683981234441881801)
            ·
              refine ⟨103500647012985925831411351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138000862683981234441881801 103500647012985925831411351)
              ·
                refine ⟨155250970519478888747117027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103500647012985925831411351 155250970519478888747117027)
                ·
                  refine ⟨232876455779218333120675541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155250970519478888747117027 232876455779218333120675541)
                  ·
                    refine ⟨5458041932325429682515833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 232876455779218333120675541 5458041932325429682515833)
                    ·
                      refine ⟨4093531449244072261886875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458041932325429682515833 4093531449244072261886875)
                      ·
                        rfl

theorem cell23_7972124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_7972124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972124 prefixEnd_7972124 := by exact prefixLift 7972124
  have htrace : WordTrace (prefixWord ++ tailWord_7972124) baseStart_7972124 baseEnd_7972124 := by
    simpa [prefixWord, tailWord_7972124, baseEnd_7972124] using wordTrace_append hprefix tailTrace_7972124
  have hstable : (prefixWord ++ tailWord_7972124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972124).length < 2 ^ (prefixWord ++ tailWord_7972124).sum := by decide
  have hdescent : baseEnd_7972124 < baseStart_7972124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972154 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_7972154 : Nat := 118140960795 + 7972154 * 2 ^ 59
def prefixEnd_7972154 : Nat := 4983230072969 + 3 ^ 40 * 7972154 * 2
def baseEnd_7972154 : Nat := 4093546853663707144511737

theorem tailTrace_7972154 : CollatzResearch.WordTrace tailWord_7972154 prefixEnd_7972154 4093546853663707144511737 := by
  unfold tailWord_7972154
  simp only [CollatzResearch.WordTrace]
  refine ⟨72692085990063767087732879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193845562640170045567287677 72692085990063767087732879)
  ·
    refine ⟨109038128985095650631599319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72692085990063767087732879 109038128985095650631599319)
    ·
      refine ⟨163557193477643475947398979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109038128985095650631599319 163557193477643475947398979)
      ·
        refine ⟨245335790216465213921098469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163557193477643475947398979 245335790216465213921098469)
        ·
          refine ⟨46000460665587227610205963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245335790216465213921098469 46000460665587227610205963)
          ·
            refine ⟨69000690998380841415308945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46000460665587227610205963 69000690998380841415308945)
            ·
              refine ⟨51750518248785631061481709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69000690998380841415308945 51750518248785631061481709)
              ·
                refine ⟨19406444343294611648055641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51750518248785631061481709 19406444343294611648055641)
                ·
                  refine ⟨14554833257470958736041731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19406444343294611648055641 14554833257470958736041731)
                  ·
                    refine ⟨21832249886206438104062597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14554833257470958736041731 21832249886206438104062597)
                    ·
                      refine ⟨4093546853663707144511737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21832249886206438104062597 4093546853663707144511737)
                      ·
                        rfl

theorem cell23_7972154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_7972154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972154 prefixEnd_7972154 := by exact prefixLift 7972154
  have htrace : WordTrace (prefixWord ++ tailWord_7972154) baseStart_7972154 baseEnd_7972154 := by
    simpa [prefixWord, tailWord_7972154, baseEnd_7972154] using wordTrace_append hprefix tailTrace_7972154
  have hstable : (prefixWord ++ tailWord_7972154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972154).length < 2 ^ (prefixWord ++ tailWord_7972154).sum := by decide
  have hdescent : baseEnd_7972154 < baseStart_7972154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972177 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 8]
def baseStart_7972177 : Nat := 118140960795 + 7972177 * 2 ^ 59
def prefixEnd_7972177 : Nat := 4983230072969 + 3 ^ 40 * 7972177 * 2
def baseEnd_7972177 : Nat := 454839851524306728280459

theorem tailTrace_7972177 : CollatzResearch.WordTrace tailWord_7972177 prefixEnd_7972177 454839851524306728280459 := by
  unfold tailWord_7972177
  simp only [CollatzResearch.WordTrace]
  refine ⟨290769182839171743279018785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193846121892781162186012523 290769182839171743279018785)
  ·
    refine ⟨218076887129378807459264089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290769182839171743279018785 218076887129378807459264089)
    ·
      refine ⟨163557665347034105594448067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218076887129378807459264089 163557665347034105594448067)
      ·
        refine ⟨245336498020551158391672101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163557665347034105594448067 245336498020551158391672101)
        ·
          refine ⟨46000593378853342198438519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245336498020551158391672101 46000593378853342198438519)
          ·
            refine ⟨69000890068280013297657779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46000593378853342198438519 69000890068280013297657779)
            ·
              refine ⟨103501335102420019946486669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69000890068280013297657779 103501335102420019946486669)
              ·
                refine ⟨38813000663407507479932501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103501335102420019946486669 38813000663407507479932501)
                ·
                  refine ⟨454839851524306728280459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38813000663407507479932501 454839851524306728280459)
                  ·
                    rfl

theorem cell23_7972177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 8].length) (baseStart_7972177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972177 prefixEnd_7972177 := by exact prefixLift 7972177
  have htrace : WordTrace (prefixWord ++ tailWord_7972177) baseStart_7972177 baseEnd_7972177 := by
    simpa [prefixWord, tailWord_7972177, baseEnd_7972177] using wordTrace_append hprefix tailTrace_7972177
  have hstable : (prefixWord ++ tailWord_7972177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972177).length < 2 ^ (prefixWord ++ tailWord_7972177).sum := by decide
  have hdescent : baseEnd_7972177 < baseStart_7972177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972181 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 3, 4]
def baseStart_7972181 : Nat := 118140960795 + 7972181 * 2 ^ 59
def prefixEnd_7972181 : Nat := 4983230072969 + 3 ^ 40 * 7972181 * 2
def baseEnd_7972181 : Nat := 1364520239213792846291371

theorem tailTrace_7972181 : CollatzResearch.WordTrace tailWord_7972181 prefixEnd_7972181 1364520239213792846291371 := by
  unfold tailWord_7972181
  simp only [CollatzResearch.WordTrace]
  refine ⟨290769328731157251962164397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193846219154104834641442931 290769328731157251962164397)
  ·
    refine ⟨109038498274183969485811649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290769328731157251962164397 109038498274183969485811649)
    ·
      refine ⟨81778873705637977114358737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109038498274183969485811649 81778873705637977114358737)
      ·
        refine ⟨61334155279228482835769053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81778873705637977114358737 61334155279228482835769053)
        ·
          refine ⟨23000308229710681063413395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61334155279228482835769053 23000308229710681063413395)
          ·
            refine ⟨34500462344566021595120093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23000308229710681063413395 34500462344566021595120093)
            ·
              refine ⟨12937673379212258098170035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34500462344566021595120093 12937673379212258098170035)
              ·
                refine ⟨19406510068818387147255053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12937673379212258098170035 19406510068818387147255053)
                ·
                  refine ⟨7277441275806895180220645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19406510068818387147255053 7277441275806895180220645)
                  ·
                    refine ⟨1364520239213792846291371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7277441275806895180220645 1364520239213792846291371)
                    ·
                      rfl

theorem cell23_7972181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_7972181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972181 prefixEnd_7972181 := by exact prefixLift 7972181
  have htrace : WordTrace (prefixWord ++ tailWord_7972181) baseStart_7972181 baseEnd_7972181 := by
    simpa [prefixWord, tailWord_7972181, baseEnd_7972181] using wordTrace_append hprefix tailTrace_7972181
  have hstable : (prefixWord ++ tailWord_7972181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972181).length < 2 ^ (prefixWord ++ tailWord_7972181).sum := by decide
  have hdescent : baseEnd_7972181 < baseStart_7972181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972224 : List Nat := [2, 1, 1, 2, 1, 2, 1, 7, 1, 5]
def baseStart_7972224 : Nat := 118140960795 + 7972224 * 2 ^ 59
def prefixEnd_7972224 : Nat := 4983230072969 + 3 ^ 40 * 7972224 * 2
def baseEnd_7972224 : Nat := 1364527599103173956878805

theorem tailTrace_7972224 : CollatzResearch.WordTrace tailWord_7972224 prefixEnd_7972224 1364527599103173956878805 := by
  unfold tailWord_7972224
  simp only [CollatzResearch.WordTrace]
  refine ⟨145385448535000735152989863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193847264713334313537319817 145385448535000735152989863)
  ·
    refine ⟨218078172802501102729484795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145385448535000735152989863 218078172802501102729484795)
    ·
      refine ⟨327117259203751654094227193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218078172802501102729484795 327117259203751654094227193)
      ·
        refine ⟨245337944402813740570670395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327117259203751654094227193 245337944402813740570670395)
        ·
          refine ⟨368006916604220610856005593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245337944402813740570670395 368006916604220610856005593)
          ·
            refine ⟨276005187453165458142004195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368006916604220610856005593 276005187453165458142004195)
            ·
              refine ⟨414007781179748187213006293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276005187453165458142004195 414007781179748187213006293)
              ·
                refine ⟨9703307371400348137804835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 414007781179748187213006293 9703307371400348137804835)
                ·
                  refine ⟨14554961057100522206707253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9703307371400348137804835 14554961057100522206707253)
                  ·
                    refine ⟨1364527599103173956878805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14554961057100522206707253 1364527599103173956878805)
                    ·
                      rfl

theorem cell23_7972224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 1, 5].length) (baseStart_7972224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972224 prefixEnd_7972224 := by exact prefixLift 7972224
  have htrace : WordTrace (prefixWord ++ tailWord_7972224) baseStart_7972224 baseEnd_7972224 := by
    simpa [prefixWord, tailWord_7972224, baseEnd_7972224] using wordTrace_append hprefix tailTrace_7972224
  have hstable : (prefixWord ++ tailWord_7972224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972224).length < 2 ^ (prefixWord ++ tailWord_7972224).sum := by decide
  have hdescent : baseEnd_7972224 < baseStart_7972224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972274 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_7972274 : Nat := 118140960795 + 7972274 * 2 ^ 59
def prefixEnd_7972274 : Nat := 4983230072969 + 3 ^ 40 * 7972274 * 2
def baseEnd_7972274 : Nat := 4093608471342246675011185

theorem tailTrace_7972274 : CollatzResearch.WordTrace tailWord_7972274 prefixEnd_7972274 4093608471342246675011185 := by
  unfold tailWord_7972274
  simp only [CollatzResearch.WordTrace]
  refine ⟨72693180179955082211324969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193848480479880219230199917 72693180179955082211324969)
  ·
    refine ⟨54519885134966311658493727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72693180179955082211324969 54519885134966311658493727)
    ·
      refine ⟨81779827702449467487740591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54519885134966311658493727 81779827702449467487740591)
      ·
        refine ⟨122669741553674201231610887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81779827702449467487740591 122669741553674201231610887)
        ·
          refine ⟨184004612330511301847416331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122669741553674201231610887 184004612330511301847416331)
          ·
            refine ⟨276006918495766952771124497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184004612330511301847416331 276006918495766952771124497)
            ·
              refine ⟨207005188871825214578343373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276006918495766952771124497 207005188871825214578343373)
              ·
                refine ⟨77626945826934455466878765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207005188871825214578343373 77626945826934455466878765)
                ·
                  refine ⟨29110104685100420800079537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77626945826934455466878765 29110104685100420800079537)
                  ·
                    refine ⟨21832578513825315600059653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29110104685100420800079537 21832578513825315600059653)
                    ·
                      refine ⟨4093608471342246675011185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21832578513825315600059653 4093608471342246675011185)
                      ·
                        rfl

theorem cell23_7972274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_7972274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972274 prefixEnd_7972274 := by exact prefixLift 7972274
  have htrace : WordTrace (prefixWord ++ tailWord_7972274) baseStart_7972274 baseEnd_7972274 := by
    simpa [prefixWord, tailWord_7972274, baseEnd_7972274] using wordTrace_append hprefix tailTrace_7972274
  have hstable : (prefixWord ++ tailWord_7972274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972274).length < 2 ^ (prefixWord ++ tailWord_7972274).sum := by decide
  have hdescent : baseEnd_7972274 < baseStart_7972274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972295 : List Nat := [1, 1, 4, 1, 1, 3, 1, 6, 1, 2, 2]
def baseStart_7972295 : Nat := 118140960795 + 7972295 * 2 ^ 59
def prefixEnd_7972295 : Nat := 4983230072969 + 3 ^ 40 * 7972295 * 2
def baseEnd_7972295 : Nat := 4093619254435991092848589

theorem tailTrace_7972295 : CollatzResearch.WordTrace tailWord_7972295 prefixEnd_7972295 4093619254435991092848589 := by
  unfold tailWord_7972295
  simp only [CollatzResearch.WordTrace]
  refine ⟨290773486652744249431814339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193848991101829499621209559 290773486652744249431814339)
  ·
    refine ⟨436160229979116374147721509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290773486652744249431814339 436160229979116374147721509)
    ·
      refine ⟨81780043121084320152697783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 436160229979116374147721509 81780043121084320152697783)
      ·
        refine ⟨122670064681626480229046675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81780043121084320152697783 122670064681626480229046675)
        ·
          refine ⟨184005097022439720343570013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122670064681626480229046675 184005097022439720343570013)
          ·
            refine ⟨69001911383414895128838755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184005097022439720343570013 69001911383414895128838755)
            ·
              refine ⟨103502867075122342693258133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69001911383414895128838755 103502867075122342693258133)
              ·
                refine ⟨4851696894146359813746475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103502867075122342693258133 4851696894146359813746475)
                ·
                  refine ⟨7277545341219539720619713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4851696894146359813746475 7277545341219539720619713)
                  ·
                    refine ⟨5458159005914654790464785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7277545341219539720619713 5458159005914654790464785)
                    ·
                      refine ⟨4093619254435991092848589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458159005914654790464785 4093619254435991092848589)
                      ·
                        rfl

theorem cell23_7972295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_7972295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972295 prefixEnd_7972295 := by exact prefixLift 7972295
  have htrace : WordTrace (prefixWord ++ tailWord_7972295) baseStart_7972295 baseEnd_7972295 := by
    simpa [prefixWord, tailWord_7972295, baseEnd_7972295] using wordTrace_append hprefix tailTrace_7972295
  have hstable : (prefixWord ++ tailWord_7972295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972295).length < 2 ^ (prefixWord ++ tailWord_7972295).sum := by decide
  have hdescent : baseEnd_7972295 < baseStart_7972295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972351 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 5, 4, 2]
def baseStart_7972351 : Nat := 118140960795 + 7972351 * 2 ^ 59
def prefixEnd_7972351 : Nat := 4983230072969 + 3 ^ 40 * 7972351 * 2
def baseEnd_7972351 : Nat := 4093648009352642873748331

theorem tailTrace_7972351 : CollatzResearch.WordTrace tailWord_7972351 prefixEnd_7972351 4093648009352642873748331 := by
  unfold tailWord_7972351
  simp only [CollatzResearch.WordTrace]
  refine ⟨290775529140541370995852907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193850352760360913997235271 290775529140541370995852907)
  ·
    refine ⟨436163293710812056493779361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290775529140541370995852907 436163293710812056493779361)
    ·
      refine ⟨327122470283109042370334521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436163293710812056493779361 327122470283109042370334521)
      ·
        refine ⟨245341852712331781777750891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327122470283109042370334521 245341852712331781777750891)
        ·
          refine ⟨368012779068497672666626337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245341852712331781777750891 368012779068497672666626337)
          ·
            refine ⟨276009584301373254499969753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368012779068497672666626337 276009584301373254499969753)
            ·
              refine ⟨207007188226029940874977315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276009584301373254499969753 207007188226029940874977315)
              ·
                refine ⟨310510782339044911312465973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207007188226029940874977315 310510782339044911312465973)
                ·
                  refine ⟨29110385844285460435543685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310510782339044911312465973 29110385844285460435543685)
                  ·
                    refine ⟨5458197345803523831664441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29110385844285460435543685 5458197345803523831664441)
                    ·
                      refine ⟨4093648009352642873748331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458197345803523831664441 4093648009352642873748331)
                      ·
                        rfl

theorem cell23_7972351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 4, 2].length) (baseStart_7972351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972351 prefixEnd_7972351 := by exact prefixLift 7972351
  have htrace : WordTrace (prefixWord ++ tailWord_7972351) baseStart_7972351 baseEnd_7972351 := by
    simpa [prefixWord, tailWord_7972351, baseEnd_7972351] using wordTrace_append hprefix tailTrace_7972351
  have hstable : (prefixWord ++ tailWord_7972351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972351).length < 2 ^ (prefixWord ++ tailWord_7972351).sum := by decide
  have hdescent : baseEnd_7972351 < baseStart_7972351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972362 : List Nat := [3, 1, 2, 2, 2, 4, 2, 1, 2, 1, 3]
def baseStart_7972362 : Nat := 118140960795 + 7972362 * 2 ^ 59
def prefixEnd_7972362 : Nat := 4983230072969 + 3 ^ 40 * 7972362 * 2
def baseEnd_7972362 : Nat := 4093653657639842330710781

theorem tailTrace_7972362 : CollatzResearch.WordTrace tailWord_7972362 prefixEnd_7972362 4093653657639842330710781 := by
  unfold tailWord_7972362
  simp only [CollatzResearch.WordTrace]
  refine ⟨72693982585875379968625835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193850620229001013249668893 72693982585875379968625835)
  ·
    refine ⟨109040973878813069952938753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72693982585875379968625835 109040973878813069952938753)
    ·
      refine ⟨81780730409109802464704065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109040973878813069952938753 81780730409109802464704065)
      ·
        refine ⟨61335547806832351848528049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81780730409109802464704065 61335547806832351848528049)
        ·
          refine ⟨46001660855124263886396037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61335547806832351848528049 46001660855124263886396037)
          ·
            refine ⟨8625311410335799478699257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46001660855124263886396037 8625311410335799478699257)
            ·
              refine ⟨6468983557751849609024443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8625311410335799478699257 6468983557751849609024443)
              ·
                refine ⟨9703475336627774413536665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6468983557751849609024443 9703475336627774413536665)
                ·
                  refine ⟨7277606502470830810152499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9703475336627774413536665 7277606502470830810152499)
                  ·
                    refine ⟨10916409753706246215228749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7277606502470830810152499 10916409753706246215228749)
                    ·
                      refine ⟨4093653657639842330710781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10916409753706246215228749 4093653657639842330710781)
                      ·
                        rfl

theorem cell23_7972362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_7972362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972362 prefixEnd_7972362 := by exact prefixLift 7972362
  have htrace : WordTrace (prefixWord ++ tailWord_7972362) baseStart_7972362 baseEnd_7972362 := by
    simpa [prefixWord, tailWord_7972362, baseEnd_7972362] using wordTrace_append hprefix tailTrace_7972362
  have hstable : (prefixWord ++ tailWord_7972362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972362).length < 2 ^ (prefixWord ++ tailWord_7972362).sum := by decide
  have hdescent : baseEnd_7972362 < baseStart_7972362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972372 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_7972372 : Nat := 118140960795 + 7972372 * 2 ^ 59
def prefixEnd_7972372 : Nat := 4983230072969 + 3 ^ 40 * 7972372 * 2
def baseEnd_7972372 : Nat := 4093658792446387291585735

theorem tailTrace_7972372 : CollatzResearch.WordTrace tailWord_7972372 prefixEnd_7972372 4093658792446387291585735 := by
  unfold tailWord_7972372
  simp only [CollatzResearch.WordTrace]
  refine ⟨145388147536732645791183685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193850863382310194388244913 145388147536732645791183685)
  ·
    refine ⟨27260277663137371085846941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145388147536732645791183685 27260277663137371085846941)
    ·
      refine ⟨10222604123676514157192603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27260277663137371085846941 10222604123676514157192603)
      ·
        refine ⟨15333906185514771235788905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10222604123676514157192603 15333906185514771235788905)
        ·
          refine ⟨11500429639136078426841679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15333906185514771235788905 11500429639136078426841679)
          ·
            refine ⟨17250644458704117640262519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11500429639136078426841679 17250644458704117640262519)
            ·
              refine ⟨25875966688056176460393779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17250644458704117640262519 25875966688056176460393779)
              ·
                refine ⟨38813950032084264690590669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25875966688056176460393779 38813950032084264690590669)
                ·
                  refine ⟨14555231262031599258971501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38813950032084264690590669 14555231262031599258971501)
                  ·
                    refine ⟨5458211723261849722114313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14555231262031599258971501 5458211723261849722114313)
                    ·
                      refine ⟨4093658792446387291585735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458211723261849722114313 4093658792446387291585735)
                      ·
                        rfl

theorem cell23_7972372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_7972372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972372 prefixEnd_7972372 := by exact prefixLift 7972372
  have htrace : WordTrace (prefixWord ++ tailWord_7972372) baseStart_7972372 baseEnd_7972372 := by
    simpa [prefixWord, tailWord_7972372, baseEnd_7972372] using wordTrace_append hprefix tailTrace_7972372
  have hstable : (prefixWord ++ tailWord_7972372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972372).length < 2 ^ (prefixWord ++ tailWord_7972372).sum := by decide
  have hdescent : baseEnd_7972372 < baseStart_7972372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972401 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 2, 3, 3]
def baseStart_7972401 : Nat := 118140960795 + 7972401 * 2 ^ 59
def prefixEnd_7972401 : Nat := 4983230072969 + 3 ^ 40 * 7972401 * 2
def baseEnd_7972401 : Nat := 4093673683385367678123101

theorem tailTrace_7972401 : CollatzResearch.WordTrace tailWord_7972401 prefixEnd_7972401 4093673683385367678123101 := by
  unfold tailWord_7972401
  simp only [CollatzResearch.WordTrace]
  refine ⟨290777352790360229535173057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193851568526906819690115371 290777352790360229535173057)
  ·
    refine ⟨218083014592770172151379793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290777352790360229535173057 218083014592770172151379793)
    ·
      refine ⟨163562260944577629113534845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218083014592770172151379793 163562260944577629113534845)
      ·
        refine ⟨61335847854216610917575567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163562260944577629113534845 61335847854216610917575567)
        ·
          refine ⟨92003771781324916376363351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61335847854216610917575567 92003771781324916376363351)
          ·
            refine ⟨138005657671987374564545027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92003771781324916376363351 138005657671987374564545027)
            ·
              refine ⟨207008486507981061846817541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138005657671987374564545027 207008486507981061846817541)
              ·
                refine ⟨38814091220246449096278289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207008486507981061846817541 38814091220246449096278289)
                ·
                  refine ⟨29110568415184836822208717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38814091220246449096278289 29110568415184836822208717)
                  ·
                    refine ⟨10916463155694313808328269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29110568415184836822208717 10916463155694313808328269)
                    ·
                      refine ⟨4093673683385367678123101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10916463155694313808328269 4093673683385367678123101)
                      ·
                        rfl

theorem cell23_7972401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_7972401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972401 prefixEnd_7972401 := by exact prefixLift 7972401
  have htrace : WordTrace (prefixWord ++ tailWord_7972401) baseStart_7972401 baseEnd_7972401 := by
    simpa [prefixWord, tailWord_7972401, baseEnd_7972401] using wordTrace_append hprefix tailTrace_7972401
  have hstable : (prefixWord ++ tailWord_7972401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972401).length < 2 ^ (prefixWord ++ tailWord_7972401).sum := by decide
  have hdescent : baseEnd_7972401 < baseStart_7972401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972408 : List Nat := [2, 1, 2, 1, 4, 3, 1, 4, 5]
def baseStart_7972408 : Nat := 118140960795 + 7972408 * 2 ^ 59
def prefixEnd_7972408 : Nat := 4983230072969 + 3 ^ 40 * 7972408 * 2
def baseEnd_7972408 : Nat := 454853030861105461192841

theorem tailTrace_7972408 : CollatzResearch.WordTrace tailWord_7972408 prefixEnd_7972408 454853030861105461192841 := by
  unfold tailWord_7972408
  simp only [CollatzResearch.WordTrace]
  refine ⟨145388804050667434865338939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193851738734223246487118585 145388804050667434865338939)
  ·
    refine ⟨218083206076001152298008409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145388804050667434865338939 218083206076001152298008409)
    ·
      refine ⟨163562404557000864223506307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218083206076001152298008409 163562404557000864223506307)
      ·
        refine ⟨245343606835501296335259461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163562404557000864223506307 245343606835501296335259461)
        ·
          refine ⟨46001926281656493062861149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245343606835501296335259461 46001926281656493062861149)
          ·
            refine ⟨17250722355621184898572931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46001926281656493062861149 17250722355621184898572931)
            ·
              refine ⟨25876083533431777347859397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17250722355621184898572931 25876083533431777347859397)
              ·
                refine ⟨4851765662518458252723637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25876083533431777347859397 4851765662518458252723637)
                ·
                  refine ⟨454853030861105461192841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4851765662518458252723637 454853030861105461192841)
                  ·
                    rfl

theorem cell23_7972408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 5].length) (baseStart_7972408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972408 prefixEnd_7972408 := by exact prefixLift 7972408
  have htrace : WordTrace (prefixWord ++ tailWord_7972408) baseStart_7972408 baseEnd_7972408 := by
    simpa [prefixWord, tailWord_7972408, baseEnd_7972408] using wordTrace_append hprefix tailTrace_7972408
  have hstable : (prefixWord ++ tailWord_7972408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972408).length < 2 ^ (prefixWord ++ tailWord_7972408).sum := by decide
  have hdescent : baseEnd_7972408 < baseStart_7972408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972491 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 3]
def baseStart_7972491 : Nat := 118140960795 + 7972491 * 2 ^ 59
def prefixEnd_7972491 : Nat := 4983230072969 + 3 ^ 40 * 7972491 * 2
def baseEnd_7972491 : Nat := 4093719896644272325997687

theorem tailTrace_7972491 : CollatzResearch.WordTrace tailWord_7972491 prefixEnd_7972491 4093719896644272325997687 := by
  unfold tailWord_7972491
  simp only [CollatzResearch.WordTrace]
  refine ⟨290780635360034174905949327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193853756906689449937299551 290780635360034174905949327)
  ·
    refine ⟨436170953040051262358923991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290780635360034174905949327 436170953040051262358923991)
    ·
      refine ⟨654256429560076893538385987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436170953040051262358923991 654256429560076893538385987)
      ·
        refine ⟨981384644340115340307578981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654256429560076893538385987 981384644340115340307578981)
        ·
          refine ⟨184009620813771626307671059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 981384644340115340307578981 184009620813771626307671059)
          ·
            refine ⟨276014431220657439461506589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184009620813771626307671059 276014431220657439461506589)
            ·
              refine ⟨103505411707746539798064971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276014431220657439461506589 103505411707746539798064971)
              ·
                refine ⟨155258117561619809697097457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103505411707746539798064971 155258117561619809697097457)
                ·
                  refine ⟨116443588171214857272823093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155258117561619809697097457 116443588171214857272823093)
                  ·
                    refine ⟨10916586391051392869327165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116443588171214857272823093 10916586391051392869327165)
                    ·
                      refine ⟨4093719896644272325997687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10916586391051392869327165 4093719896644272325997687)
                      ·
                        rfl

theorem cell23_7972491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 3].length) (baseStart_7972491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972491 prefixEnd_7972491 := by exact prefixLift 7972491
  have htrace : WordTrace (prefixWord ++ tailWord_7972491) baseStart_7972491 baseEnd_7972491 := by
    simpa [prefixWord, tailWord_7972491, baseEnd_7972491] using wordTrace_append hprefix tailTrace_7972491
  have hstable : (prefixWord ++ tailWord_7972491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972491).length < 2 ^ (prefixWord ++ tailWord_7972491).sum := by decide
  have hdescent : baseEnd_7972491 < baseStart_7972491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972546 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_7972546 : Nat := 118140960795 + 7972546 * 2 ^ 59
def prefixEnd_7972546 : Nat := 4983230072969 + 3 ^ 40 * 7972546 * 2
def baseEnd_7972546 : Nat := 4093748138080269610809935

theorem tailTrace_7972546 : CollatzResearch.WordTrace tailWord_7972546 prefixEnd_7972546 4093748138080269610809935 := by
  unfold tailWord_7972546
  simp only [CollatzResearch.WordTrace]
  refine ⟨72695660343708729824800373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193855094249889946199467661 72695660343708729824800373)
  ·
    refine ⟨6815218157222693421075035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72695660343708729824800373 6815218157222693421075035)
    ·
      refine ⟨10222827235834040131612553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6815218157222693421075035 10222827235834040131612553)
      ·
        refine ⟨7667120426875530098709415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10222827235834040131612553 7667120426875530098709415)
        ·
          refine ⟨11500680640313295148064123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7667120426875530098709415 11500680640313295148064123)
          ·
            refine ⟨17251020960469942722096185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11500680640313295148064123 17251020960469942722096185)
            ·
              refine ⟨12938265720352457041572139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17251020960469942722096185 12938265720352457041572139)
              ·
                refine ⟨19407398580528685562358209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12938265720352457041572139 19407398580528685562358209)
                ·
                  refine ⟨14555548935396514171768657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19407398580528685562358209 14555548935396514171768657)
                  ·
                    refine ⟨10916661701547385628826493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14555548935396514171768657 10916661701547385628826493)
                    ·
                      refine ⟨4093748138080269610809935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10916661701547385628826493 4093748138080269610809935)
                      ·
                        rfl

theorem cell23_7972546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_7972546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972546 prefixEnd_7972546 := by exact prefixLift 7972546
  have htrace : WordTrace (prefixWord ++ tailWord_7972546) baseStart_7972546 baseEnd_7972546 := by
    simpa [prefixWord, tailWord_7972546, baseEnd_7972546] using wordTrace_append hprefix tailTrace_7972546
  have hstable : (prefixWord ++ tailWord_7972546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972546).length < 2 ^ (prefixWord ++ tailWord_7972546).sum := by decide
  have hdescent : baseEnd_7972546 < baseStart_7972546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972558 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_7972558 : Nat := 118140960795 + 7972558 * 2 ^ 59
def prefixEnd_7972558 : Nat := 4983230072969 + 3 ^ 40 * 7972558 * 2
def baseEnd_7972558 : Nat := 1364584766616041187953293

theorem tailTrace_7972558 : CollatzResearch.WordTrace tailWord_7972558 prefixEnd_7972558 1364584766616041187953293 := by
  unfold tailWord_7972558
  simp only [CollatzResearch.WordTrace]
  refine ⟨36347884881348930668579791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193855386033860963565758885 36347884881348930668579791)
  ·
    refine ⟨54521827322023396002869687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36347884881348930668579791 54521827322023396002869687)
    ·
      refine ⟨81782740983035094004304531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54521827322023396002869687 81782740983035094004304531)
      ·
        refine ⟨122674111474552641006456797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81782740983035094004304531 122674111474552641006456797)
        ·
          refine ⟨46002791802957240377421299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122674111474552641006456797 46002791802957240377421299)
          ·
            refine ⟨69004187704435860566131949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46002791802957240377421299 69004187704435860566131949)
            ·
              refine ⟨25876570389163447712299481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69004187704435860566131949 25876570389163447712299481)
              ·
                refine ⟨19407427791872585784224611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25876570389163447712299481 19407427791872585784224611)
                ·
                  refine ⟨29111141687808878676336917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19407427791872585784224611 29111141687808878676336917)
                  ·
                    refine ⟨1364584766616041187953293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29111141687808878676336917 1364584766616041187953293)
                    ·
                      rfl

theorem cell23_7972558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_7972558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972558 prefixEnd_7972558 := by exact prefixLift 7972558
  have htrace : WordTrace (prefixWord ++ tailWord_7972558) baseStart_7972558 baseEnd_7972558 := by
    simpa [prefixWord, tailWord_7972558, baseEnd_7972558] using wordTrace_append hprefix tailTrace_7972558
  have hstable : (prefixWord ++ tailWord_7972558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972558).length < 2 ^ (prefixWord ++ tailWord_7972558).sum := by decide
  have hdescent : baseEnd_7972558 < baseStart_7972558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972562 : List Nat := [3, 2, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_7972562 : Nat := 118140960795 + 7972562 * 2 ^ 59
def prefixEnd_7972562 : Nat := 4983230072969 + 3 ^ 40 * 7972562 * 2
def baseEnd_7972562 : Nat := 1364585451256913849403287

theorem tailTrace_7972562 : CollatzResearch.WordTrace tailWord_7972562 prefixEnd_7972562 1364585451256913849403287 := by
  unfold tailWord_7972562
  simp only [CollatzResearch.WordTrace]
  refine ⟨72695806235694238507945985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193855483295184636021189293 72695806235694238507945985)
  ·
    refine ⟨54521854676770678880959489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72695806235694238507945985 54521854676770678880959489)
    ·
      refine ⟨40891391007578009160719617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54521854676770678880959489 40891391007578009160719617)
      ·
        refine ⟨30668543255683506870539713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40891391007578009160719617 30668543255683506870539713)
        ·
          refine ⟨23001407441762630152904785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30668543255683506870539713 23001407441762630152904785)
          ·
            refine ⟨17251055581321972614678589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23001407441762630152904785 17251055581321972614678589)
            ·
              refine ⟨6469145842995739730504471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17251055581321972614678589 6469145842995739730504471)
              ·
                refine ⟨9703718764493609595756707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6469145842995739730504471 9703718764493609595756707)
                ·
                  refine ⟨14555578146740414393635061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9703718764493609595756707 14555578146740414393635061)
                  ·
                    refine ⟨1364585451256913849403287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14555578146740414393635061 1364585451256913849403287)
                    ·
                      rfl

theorem cell23_7972562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_7972562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972562 prefixEnd_7972562 := by exact prefixLift 7972562
  have htrace : WordTrace (prefixWord ++ tailWord_7972562) baseStart_7972562 baseEnd_7972562 := by
    simpa [prefixWord, tailWord_7972562, baseEnd_7972562] using wordTrace_append hprefix tailTrace_7972562
  have hstable : (prefixWord ++ tailWord_7972562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972562).length < 2 ^ (prefixWord ++ tailWord_7972562).sum := by decide
  have hdescent : baseEnd_7972562 < baseStart_7972562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972575 : List Nat := [1, 1, 2, 3, 2, 2, 4, 2, 2, 4]
def baseStart_7972575 : Nat := 118140960795 + 7972575 * 2 ^ 59
def prefixEnd_7972575 : Nat := 4983230072969 + 3 ^ 40 * 7972575 * 2
def baseEnd_7972575 : Nat := 1364587676339749999115767

theorem tailTrace_7972575 : CollatzResearch.WordTrace tailWord_7972575 prefixEnd_7972575 1364587676339749999115767 := by
  unfold tailWord_7972575
  simp only [CollatzResearch.WordTrace]
  refine ⟨290783699091729857252007179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193855799394486571501338119 290783699091729857252007179)
  ·
    refine ⟨436175548637594785878010769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290783699091729857252007179 436175548637594785878010769)
    ·
      refine ⟨327131661478196089408508077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436175548637594785878010769 327131661478196089408508077)
      ·
        refine ⟨122674373054323533528190529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327131661478196089408508077 122674373054323533528190529)
        ·
          refine ⟨92005779790742650146142897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122674373054323533528190529 92005779790742650146142897)
          ·
            refine ⟨69004334843056987609607173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92005779790742650146142897 69004334843056987609607173)
            ·
              refine ⟨12938312783073185176801345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69004334843056987609607173 12938312783073185176801345)
              ·
                refine ⟨9703734587304888882601009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12938312783073185176801345 9703734587304888882601009)
                ·
                  refine ⟨7277800940478666661950757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9703734587304888882601009 7277800940478666661950757)
                  ·
                    refine ⟨1364587676339749999115767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7277800940478666661950757 1364587676339749999115767)
                    ·
                      rfl

theorem cell23_7972575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 4].length) (baseStart_7972575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972575 prefixEnd_7972575 := by exact prefixLift 7972575
  have htrace : WordTrace (prefixWord ++ tailWord_7972575) baseStart_7972575 baseEnd_7972575 := by
    simpa [prefixWord, tailWord_7972575, baseEnd_7972575] using wordTrace_append hprefix tailTrace_7972575
  have hstable : (prefixWord ++ tailWord_7972575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972575).length < 2 ^ (prefixWord ++ tailWord_7972575).sum := by decide
  have hdescent : baseEnd_7972575 < baseStart_7972575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972632 : List Nat := [2, 1, 2, 3, 1, 1, 5, 2, 2, 1, 3]
def baseStart_7972632 : Nat := 118140960795 + 7972632 * 2 ^ 59
def prefixEnd_7972632 : Nat := 4983230072969 + 3 ^ 40 * 7972632 * 2
def baseEnd_7972632 : Nat := 4093792297416556274334539

theorem tailTrace_7972632 : CollatzResearch.WordTrace tailWord_7972632 prefixEnd_7972632 4093792297416556274334539 := by
  unfold tailWord_7972632
  simp only [CollatzResearch.WordTrace]
  refine ⟨145392889026261677993416075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193857185368348903991221433 145392889026261677993416075)
  ·
    refine ⟨218089333539392516990124113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145392889026261677993416075 218089333539392516990124113)
    ·
      refine ⟨163567000154544387742593085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218089333539392516990124113 163567000154544387742593085)
      ·
        refine ⟨61337625057954145403472407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163567000154544387742593085 61337625057954145403472407)
        ·
          refine ⟨92006437586931218105208611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61337625057954145403472407 92006437586931218105208611)
          ·
            refine ⟨138009656380396827157812917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92006437586931218105208611 138009656380396827157812917)
            ·
              refine ⟨12938405285662202546044961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138009656380396827157812917 12938405285662202546044961)
              ·
                refine ⟨9703803964246651909533721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12938405285662202546044961 9703803964246651909533721)
                ·
                  refine ⟨7277852973184988932150291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9703803964246651909533721 7277852973184988932150291)
                  ·
                    refine ⟨10916779459777483398225437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7277852973184988932150291 10916779459777483398225437)
                    ·
                      refine ⟨4093792297416556274334539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10916779459777483398225437 4093792297416556274334539)
                      ·
                        rfl

theorem cell23_7972632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_7972632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972632 prefixEnd_7972632 := by exact prefixLift 7972632
  have htrace : WordTrace (prefixWord ++ tailWord_7972632) baseStart_7972632 baseEnd_7972632 := by
    simpa [prefixWord, tailWord_7972632, baseEnd_7972632] using wordTrace_append hprefix tailTrace_7972632
  have hstable : (prefixWord ++ tailWord_7972632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972632).length < 2 ^ (prefixWord ++ tailWord_7972632).sum := by decide
  have hdescent : baseEnd_7972632 < baseStart_7972632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972659 : List Nat := [1, 1, 1, 2, 7, 1, 2, 2, 1, 3, 2]
def baseStart_7972659 : Nat := 118140960795 + 7972659 * 2 ^ 59
def prefixEnd_7972659 : Nat := 4983230072969 + 3 ^ 40 * 7972659 * 2
def baseEnd_7972659 : Nat := 4093806161394227668696915

theorem tailTrace_7972659 : CollatzResearch.WordTrace tailWord_7972659 prefixEnd_7972659 4093806161394227668696915 := by
  unfold tailWord_7972659
  simp only [CollatzResearch.WordTrace]
  refine ⟨290786762823425539598065031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193857841882283693065376687 290786762823425539598065031)
  ·
    refine ⟨436180144235138309397097547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290786762823425539598065031 436180144235138309397097547)
    ·
      refine ⟨654270216352707464095646321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436180144235138309397097547 654270216352707464095646321)
      ·
        refine ⟨490702662264530598071734741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654270216352707464095646321 490702662264530598071734741)
        ·
          refine ⟨11500843646824935892306283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 490702662264530598071734741 11500843646824935892306283)
          ·
            refine ⟨17251265470237403838459425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11500843646824935892306283 17251265470237403838459425)
            ·
              refine ⟨12938449102678052878844569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17251265470237403838459425 12938449102678052878844569)
              ·
                refine ⟨9703836827008539659133427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12938449102678052878844569 9703836827008539659133427)
                ·
                  refine ⟨14555755240512809488700141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9703836827008539659133427 14555755240512809488700141)
                  ·
                    refine ⟨5458408215192303558262553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14555755240512809488700141 5458408215192303558262553)
                    ·
                      refine ⟨4093806161394227668696915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458408215192303558262553 4093806161394227668696915)
                      ·
                        rfl

theorem cell23_7972659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 3, 2].length) (baseStart_7972659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972659 prefixEnd_7972659 := by exact prefixLift 7972659
  have htrace : WordTrace (prefixWord ++ tailWord_7972659) baseStart_7972659 baseEnd_7972659 := by
    simpa [prefixWord, tailWord_7972659, baseEnd_7972659] using wordTrace_append hprefix tailTrace_7972659
  have hstable : (prefixWord ++ tailWord_7972659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972659).length < 2 ^ (prefixWord ++ tailWord_7972659).sum := by decide
  have hdescent : baseEnd_7972659 < baseStart_7972659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972668 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_7972668 : Nat := 118140960795 + 7972668 * 2 ^ 59
def prefixEnd_7972668 : Nat := 4983230072969 + 3 ^ 40 * 7972668 * 2
def baseEnd_7972668 : Nat := 4093810782720118133484373

theorem tailTrace_7972668 : CollatzResearch.WordTrace tailWord_7972668 prefixEnd_7972668 4093810782720118133484373 := by
  unfold tailWord_7972668
  simp only [CollatzResearch.WordTrace]
  refine ⟨145393545540196467067571329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193858060720261956090095105 145393545540196467067571329)
  ·
    refine ⟨109045159155147350300678497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145393545540196467067571329 109045159155147350300678497)
    ·
      refine ⟨81783869366360512725508873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109045159155147350300678497 81783869366360512725508873)
      ·
        refine ⟨61337902024770384544131655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81783869366360512725508873 61337902024770384544131655)
        ·
          refine ⟨92006853037155576816197483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61337902024770384544131655 92006853037155576816197483)
          ·
            refine ⟨138010279555733365224296225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92006853037155576816197483 138010279555733365224296225)
            ·
              refine ⟨103507709666800023918222169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138010279555733365224296225 103507709666800023918222169)
              ·
                refine ⟨77630782250100017938666627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103507709666800023918222169 77630782250100017938666627)
                ·
                  refine ⟨116446173375150026907999941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77630782250100017938666627 116446173375150026907999941)
                  ·
                    refine ⟨21833657507840630045249989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116446173375150026907999941 21833657507840630045249989)
                    ·
                      refine ⟨4093810782720118133484373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21833657507840630045249989 4093810782720118133484373)
                      ·
                        rfl

theorem cell23_7972668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_7972668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972668 prefixEnd_7972668 := by exact prefixLift 7972668
  have htrace : WordTrace (prefixWord ++ tailWord_7972668) baseStart_7972668 baseEnd_7972668 := by
    simpa [prefixWord, tailWord_7972668, baseEnd_7972668] using wordTrace_append hprefix tailTrace_7972668
  have hstable : (prefixWord ++ tailWord_7972668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972668).length < 2 ^ (prefixWord ++ tailWord_7972668).sum := by decide
  have hdescent : baseEnd_7972668 < baseStart_7972668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972706 : List Nat := [3, 3, 2, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_7972706 : Nat := 118140960795 + 7972706 * 2 ^ 59
def prefixEnd_7972706 : Nat := 4983230072969 + 3 ^ 40 * 7972706 * 2
def baseEnd_7972706 : Nat := 4093830294984988984809199

theorem tailTrace_7972706 : CollatzResearch.WordTrace tailWord_7972706 prefixEnd_7972706 4093830294984988984809199 := by
  unfold tailWord_7972706
  simp only [CollatzResearch.WordTrace]
  refine ⟨72697119263563816656256493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193858984702836844416683981 72697119263563816656256493)
  ·
    refine ⟨27261419723836431246096185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72697119263563816656256493 27261419723836431246096185)
    ·
      refine ⟨20446064792877323434572139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27261419723836431246096185 20446064792877323434572139)
      ·
        refine ⟨30669097189315985151858209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20446064792877323434572139 30669097189315985151858209)
        ·
          refine ⟨23001822891986988863893657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30669097189315985151858209 23001822891986988863893657)
          ·
            refine ⟨17251367168990241647920243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23001822891986988863893657 17251367168990241647920243)
            ·
              refine ⟨25877050753485362471880365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17251367168990241647920243 25877050753485362471880365)
              ·
                refine ⟨9703894032557010926955137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25877050753485362471880365 9703894032557010926955137)
                ·
                  refine ⟨7277920524417758195216353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9703894032557010926955137 7277920524417758195216353)
                  ·
                    refine ⟨5458440393313318646412265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7277920524417758195216353 5458440393313318646412265)
                    ·
                      refine ⟨4093830294984988984809199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458440393313318646412265 4093830294984988984809199)
                      ·
                        rfl

theorem cell23_7972706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_7972706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972706 prefixEnd_7972706 := by exact prefixLift 7972706
  have htrace : WordTrace (prefixWord ++ tailWord_7972706) baseStart_7972706 baseEnd_7972706 := by
    simpa [prefixWord, tailWord_7972706, baseEnd_7972706] using wordTrace_append hprefix tailTrace_7972706
  have hstable : (prefixWord ++ tailWord_7972706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972706).length < 2 ^ (prefixWord ++ tailWord_7972706).sum := by decide
  have hdescent : baseEnd_7972706 < baseStart_7972706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972728 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_7972728 : Nat := 118140960795 + 7972728 * 2 ^ 59
def prefixEnd_7972728 : Nat := 4983230072969 + 3 ^ 40 * 7972728 * 2
def baseEnd_7972728 : Nat := 4093841591559387898734097

theorem tailTrace_7972728 : CollatzResearch.WordTrace tailWord_7972728 prefixEnd_7972728 4093841591559387898734097 := by
  unfold tailWord_7972728
  simp only [CollatzResearch.WordTrace]
  refine ⟨145394639730087782191163419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193859519640117042921551225 145394639730087782191163419)
  ·
    refine ⟨218091959595131673286745129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145394639730087782191163419 218091959595131673286745129)
    ·
      refine ⟨163568969696348754965058847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218091959595131673286745129 163568969696348754965058847)
      ·
        refine ⟨245353454544523132447588271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163568969696348754965058847 245353454544523132447588271)
        ·
          refine ⟨368030181816784698671382407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245353454544523132447588271 368030181816784698671382407)
          ·
            refine ⟨552045272725177048007073611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368030181816784698671382407 552045272725177048007073611)
            ·
              refine ⟨828067909087765572010610417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552045272725177048007073611 828067909087765572010610417)
              ·
                refine ⟨621050931815824179007957813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828067909087765572010610417 621050931815824179007957813)
                ·
                  refine ⟨58223524857733516781996045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 621050931815824179007957813 58223524857733516781996045)
                  ·
                    refine ⟨21833821821650068793248517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58223524857733516781996045 21833821821650068793248517)
                    ·
                      refine ⟨4093841591559387898734097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21833821821650068793248517 4093841591559387898734097)
                      ·
                        rfl

theorem cell23_7972728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_7972728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972728 prefixEnd_7972728 := by exact prefixLift 7972728
  have htrace : WordTrace (prefixWord ++ tailWord_7972728) baseStart_7972728 baseEnd_7972728 := by
    simpa [prefixWord, tailWord_7972728, baseEnd_7972728] using wordTrace_append hprefix tailTrace_7972728
  have hstable : (prefixWord ++ tailWord_7972728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972728).length < 2 ^ (prefixWord ++ tailWord_7972728).sum := by decide
  have hdescent : baseEnd_7972728 < baseStart_7972728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972745 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 2, 1, 4]
def baseStart_7972745 : Nat := 118140960795 + 7972745 * 2 ^ 59
def prefixEnd_7972745 : Nat := 4983230072969 + 3 ^ 40 * 7972745 * 2
def baseEnd_7972745 : Nat := 4093850320730514332221519

theorem tailTrace_7972745 : CollatzResearch.WordTrace tailWord_7972745 prefixEnd_7972745 4093850320730514332221519 := by
  unfold tailWord_7972745
  simp only [CollatzResearch.WordTrace]
  refine ⟨290789899501113976285695689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193859933000742650857130459 290789899501113976285695689)
  ·
    refine ⟨218092424625835482214271767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290789899501113976285695689 218092424625835482214271767)
    ·
      refine ⟨327138636938753223321407651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218092424625835482214271767 327138636938753223321407651)
      ·
        refine ⟨490707955408129834982111477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327138636938753223321407651 490707955408129834982111477)
        ·
          refine ⟨46003870819512172029572951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 490707955408129834982111477 46003870819512172029572951)
          ·
            refine ⟨69005806229268258044359427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46003870819512172029572951 69005806229268258044359427)
            ·
              refine ⟨103508709343902387066539141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69005806229268258044359427 103508709343902387066539141)
              ·
                refine ⟨19407883001981697574976089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103508709343902387066539141 19407883001981697574976089)
                ·
                  refine ⟨14555912251486273181232067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19407883001981697574976089 14555912251486273181232067)
                  ·
                    refine ⟨21833868377229409771848101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14555912251486273181232067 21833868377229409771848101)
                    ·
                      refine ⟨4093850320730514332221519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21833868377229409771848101 4093850320730514332221519)
                      ·
                        rfl

theorem cell23_7972745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_7972745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972745 prefixEnd_7972745 := by exact prefixLift 7972745
  have htrace : WordTrace (prefixWord ++ tailWord_7972745) baseStart_7972745 baseEnd_7972745 := by
    simpa [prefixWord, tailWord_7972745, baseEnd_7972745] using wordTrace_append hprefix tailTrace_7972745
  have hstable : (prefixWord ++ tailWord_7972745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972745).length < 2 ^ (prefixWord ++ tailWord_7972745).sum := by decide
  have hdescent : baseEnd_7972745 < baseStart_7972745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972746 : List Nat := [3, 1, 2, 4, 2, 2, 2, 2, 5]
def baseStart_7972746 : Nat := 118140960795 + 7972746 * 2 ^ 59
def prefixEnd_7972746 : Nat := 4983230072969 + 3 ^ 40 * 7972746 * 2
def baseEnd_7972746 : Nat := 454872314912352092034335

theorem tailTrace_7972746 : CollatzResearch.WordTrace tailWord_7972746 prefixEnd_7972746 454872314912352092034335 := by
  unfold tailWord_7972746
  simp only [CollatzResearch.WordTrace]
  refine ⟨72697483993527588364120523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193859957316073568970988061 72697483993527588364120523)
  ·
    refine ⟨109046225990291382546180785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72697483993527588364120523 109046225990291382546180785)
    ·
      refine ⟨81784669492718536909635589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109046225990291382546180785 81784669492718536909635589)
      ·
        refine ⟨15334625529884725670556673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81784669492718536909635589 15334625529884725670556673)
        ·
          refine ⟨11500969147413544252917505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15334625529884725670556673 11500969147413544252917505)
          ·
            refine ⟨8625726860560158189688129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11500969147413544252917505 8625726860560158189688129)
            ·
              refine ⟨6469295145420118642266097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8625726860560158189688129 6469295145420118642266097)
              ·
                refine ⟨4851971359065088981699573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6469295145420118642266097 4851971359065088981699573)
                ·
                  refine ⟨454872314912352092034335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4851971359065088981699573 454872314912352092034335)
                  ·
                    rfl

theorem cell23_7972746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 5].length) (baseStart_7972746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972746 prefixEnd_7972746 := by exact prefixLift 7972746
  have htrace : WordTrace (prefixWord ++ tailWord_7972746) baseStart_7972746 baseEnd_7972746 := by
    simpa [prefixWord, tailWord_7972746, baseEnd_7972746] using wordTrace_append hprefix tailTrace_7972746
  have hstable : (prefixWord ++ tailWord_7972746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972746).length < 2 ^ (prefixWord ++ tailWord_7972746).sum := by decide
  have hdescent : baseEnd_7972746 < baseStart_7972746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972748 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_7972748 : Nat := 118140960795 + 7972748 * 2 ^ 59
def prefixEnd_7972748 : Nat := 4983230072969 + 3 ^ 40 * 7972748 * 2
def baseEnd_7972748 : Nat := 4093851861172477820484005

theorem tailTrace_7972748 : CollatzResearch.WordTrace tailWord_7972748 prefixEnd_7972748 4093851861172477820484005 := by
  unfold tailWord_7972748
  simp only [CollatzResearch.WordTrace]
  refine ⟨145395004460051553899027449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193860005946735405198703265 145395004460051553899027449)
  ·
    refine ⟨109046253345038665424270587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145395004460051553899027449 109046253345038665424270587)
    ·
      refine ⟨163569380017557998136405881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109046253345038665424270587 163569380017557998136405881)
      ·
        refine ⟨122677035013168498602304411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163569380017557998136405881 122677035013168498602304411)
        ·
          refine ⟨184015552519752747903456617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122677035013168498602304411 184015552519752747903456617)
          ·
            refine ⟨138011664389814560927592463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184015552519752747903456617 138011664389814560927592463)
            ·
              refine ⟨207017496584721841391388695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138011664389814560927592463 207017496584721841391388695)
              ·
                refine ⟨310526244877082762087083043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207017496584721841391388695 310526244877082762087083043)
                ·
                  refine ⟨465789367315624143130624565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310526244877082762087083043 465789367315624143130624565)
                  ·
                    refine ⟨43667753185839763418496053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 465789367315624143130624565 43667753185839763418496053)
                    ·
                      refine ⟨4093851861172477820484005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43667753185839763418496053 4093851861172477820484005)
                      ·
                        rfl

theorem cell23_7972748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_7972748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972748 prefixEnd_7972748 := by exact prefixLift 7972748
  have htrace : WordTrace (prefixWord ++ tailWord_7972748) baseStart_7972748 baseEnd_7972748 := by
    simpa [prefixWord, tailWord_7972748, baseEnd_7972748] using wordTrace_append hprefix tailTrace_7972748
  have hstable : (prefixWord ++ tailWord_7972748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972748).length < 2 ^ (prefixWord ++ tailWord_7972748).sum := by decide
  have hdescent : baseEnd_7972748 < baseStart_7972748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972762 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2]
def baseStart_7972762 : Nat := 118140960795 + 7972762 * 2 ^ 59
def prefixEnd_7972762 : Nat := 4983230072969 + 3 ^ 40 * 7972762 * 2
def baseEnd_7972762 : Nat := 4093859049901640765708941

theorem tailTrace_7972762 : CollatzResearch.WordTrace tailWord_7972762 prefixEnd_7972762 4093859049901640765708941 := by
  unfold tailWord_7972762
  simp only [CollatzResearch.WordTrace]
  refine ⟨72697629885513097047266135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193860346361368258792709693 72697629885513097047266135)
  ·
    refine ⟨109046444828269645570899203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72697629885513097047266135 109046444828269645570899203)
    ·
      refine ⟨163569667242404468356348805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109046444828269645570899203 163569667242404468356348805)
      ·
        refine ⟨30669312607950837816815401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163569667242404468356348805 30669312607950837816815401)
        ·
          refine ⟨23001984455963128362611551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30669312607950837816815401 23001984455963128362611551)
          ·
            refine ⟨34502976683944692543917327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23001984455963128362611551 34502976683944692543917327)
            ·
              refine ⟨51754465025917038815875991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34502976683944692543917327 51754465025917038815875991)
              ·
                refine ⟨77631697538875558223813987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51754465025917038815875991 77631697538875558223813987)
                ·
                  refine ⟨116447546308313337335720981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77631697538875558223813987 116447546308313337335720981)
                  ·
                    refine ⟨5458478733202187687611921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116447546308313337335720981 5458478733202187687611921)
                    ·
                      refine ⟨4093859049901640765708941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458478733202187687611921 4093859049901640765708941)
                      ·
                        rfl

theorem cell23_7972762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_7972762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972762 prefixEnd_7972762 := by exact prefixLift 7972762
  have htrace : WordTrace (prefixWord ++ tailWord_7972762) baseStart_7972762 baseEnd_7972762 := by
    simpa [prefixWord, tailWord_7972762, baseEnd_7972762] using wordTrace_append hprefix tailTrace_7972762
  have hstable : (prefixWord ++ tailWord_7972762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972762).length < 2 ^ (prefixWord ++ tailWord_7972762).sum := by decide
  have hdescent : baseEnd_7972762 < baseStart_7972762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972768 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 10]
def baseStart_7972768 : Nat := 118140960795 + 7972768 * 2 ^ 59
def prefixEnd_7972768 : Nat := 4983230072969 + 3 ^ 40 * 7972768 * 2
def baseEnd_7972768 : Nat := 454873570087285304692657

theorem tailTrace_7972768 : CollatzResearch.WordTrace tailWord_7972768 prefixEnd_7972768 454873570087285304692657 := by
  unfold tailWord_7972768
  simp only [CollatzResearch.WordTrace]
  refine ⟨145395369190015325606891479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193860492253353767475855305 145395369190015325606891479)
  ·
    refine ⟨218093053785022988410337219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145395369190015325606891479 218093053785022988410337219)
    ·
      refine ⟨327139580677534482615505829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218093053785022988410337219 327139580677534482615505829)
      ·
        refine ⟨61338671377037715490407343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327139580677534482615505829 61338671377037715490407343)
        ·
          refine ⟨92008007065556573235611015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61338671377037715490407343 92008007065556573235611015)
          ·
            refine ⟨138012010598334859853416523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92008007065556573235611015 138012010598334859853416523)
            ·
              refine ⟨207018015897502289780124785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138012010598334859853416523 207018015897502289780124785)
              ·
                refine ⟨155263511923126717335093589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207018015897502289780124785 155263511923126717335093589)
                ·
                  refine ⟨454873570087285304692657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 155263511923126717335093589 454873570087285304692657)
                  ·
                    rfl

theorem cell23_7972768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 10].length) (baseStart_7972768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972768 prefixEnd_7972768 := by exact prefixLift 7972768
  have htrace : WordTrace (prefixWord ++ tailWord_7972768) baseStart_7972768 baseEnd_7972768 := by
    simpa [prefixWord, tailWord_7972768, baseEnd_7972768] using wordTrace_append hprefix tailTrace_7972768
  have hstable : (prefixWord ++ tailWord_7972768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972768).length < 2 ^ (prefixWord ++ tailWord_7972768).sum := by decide
  have hdescent : baseEnd_7972768 < baseStart_7972768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972772 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_7972772 : Nat := 118140960795 + 7972772 * 2 ^ 59
def prefixEnd_7972772 : Nat := 4983230072969 + 3 ^ 40 * 7972772 * 2
def baseEnd_7972772 : Nat := 1364621394902728575527965

theorem tailTrace_7972772 : CollatzResearch.WordTrace tailWord_7972772 prefixEnd_7972772 1364621394902728575527965 := by
  unfold tailWord_7972772
  simp only [CollatzResearch.WordTrace]
  refine ⟨145395442136008079948464285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193860589514677439931285713 145395442136008079948464285)
  ·
    refine ⟨54523290801003029980674107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145395442136008079948464285 54523290801003029980674107)
    ·
      refine ⟨81784936201504544971011161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54523290801003029980674107 81784936201504544971011161)
      ·
        refine ⟨61338702151128408728258371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81784936201504544971011161 61338702151128408728258371)
        ·
          refine ⟨92008053226692613092387557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61338702151128408728258371 92008053226692613092387557)
          ·
            refine ⟨17251509980004864954822667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92008053226692613092387557 17251509980004864954822667)
            ·
              refine ⟨25877264970007297432234001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17251509980004864954822667 25877264970007297432234001)
              ·
                refine ⟨19407948727505473074175501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25877264970007297432234001 19407948727505473074175501)
                ·
                  refine ⟨7277980772814552402815813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19407948727505473074175501 7277980772814552402815813)
                  ·
                    refine ⟨1364621394902728575527965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7277980772814552402815813 1364621394902728575527965)
                    ·
                      rfl

theorem cell23_7972772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_7972772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972772 prefixEnd_7972772 := by exact prefixLift 7972772
  have htrace : WordTrace (prefixWord ++ tailWord_7972772) baseStart_7972772 baseEnd_7972772 := by
    simpa [prefixWord, tailWord_7972772, baseEnd_7972772] using wordTrace_append hprefix tailTrace_7972772
  have hstable : (prefixWord ++ tailWord_7972772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972772).length < 2 ^ (prefixWord ++ tailWord_7972772).sum := by decide
  have hdescent : baseEnd_7972772 < baseStart_7972772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972776 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 2, 5]
def baseStart_7972776 : Nat := 118140960795 + 7972776 * 2 ^ 59
def prefixEnd_7972776 : Nat := 4983230072969 + 3 ^ 40 * 7972776 * 2
def baseEnd_7972776 : Nat := 1364622079543601236977959

theorem tailTrace_7972776 : CollatzResearch.WordTrace tailWord_7972776 prefixEnd_7972776 1364622079543601236977959 := by
  unfold tailWord_7972776
  simp only [CollatzResearch.WordTrace]
  refine ⟨145395515082000834290037091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193860686776001112386716121 145395515082000834290037091)
  ·
    refine ⟨218093272623001251435055637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145395515082000834290037091 218093272623001251435055637)
    ·
      refine ⟨10223122154203183661018233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 218093272623001251435055637 10223122154203183661018233)
      ·
        refine ⟨7667341615652387745763675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10223122154203183661018233 7667341615652387745763675)
        ·
          refine ⟨11501012423478581618645513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7667341615652387745763675 11501012423478581618645513)
          ·
            refine ⟨8625759317608936213984135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11501012423478581618645513 8625759317608936213984135)
            ·
              refine ⟨12938638976413404320976203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8625759317608936213984135 12938638976413404320976203)
              ·
                refine ⟨19407958464620106481464305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12938638976413404320976203 19407958464620106481464305)
                ·
                  refine ⟨14555968848465079861098229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19407958464620106481464305 14555968848465079861098229)
                  ·
                    refine ⟨1364622079543601236977959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14555968848465079861098229 1364622079543601236977959)
                    ·
                      rfl

theorem cell23_7972776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_7972776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972776 prefixEnd_7972776 := by exact prefixLift 7972776
  have htrace : WordTrace (prefixWord ++ tailWord_7972776) baseStart_7972776 baseEnd_7972776 := by
    simpa [prefixWord, tailWord_7972776, baseEnd_7972776] using wordTrace_append hprefix tailTrace_7972776
  have hstable : (prefixWord ++ tailWord_7972776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972776).length < 2 ^ (prefixWord ++ tailWord_7972776).sum := by decide
  have hdescent : baseEnd_7972776 < baseStart_7972776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972789 : List Nat := [1, 3, 3, 2, 1, 2, 1, 5, 1, 4]
def baseStart_7972789 : Nat := 118140960795 + 7972789 * 2 ^ 59
def prefixEnd_7972789 : Nat := 4983230072969 + 3 ^ 40 * 7972789 * 2
def baseEnd_7972789 : Nat := 1364624304626437386690439

theorem tailTrace_7972789 : CollatzResearch.WordTrace tailWord_7972789 prefixEnd_7972789 1364624304626437386690439 := by
  unfold tailWord_7972789
  simp only [CollatzResearch.WordTrace]
  refine ⟨290791504312954571800297421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193861002875303047866864947 290791504312954571800297421)
  ·
    refine ⟨109046814117357964425111533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290791504312954571800297421 109046814117357964425111533)
    ·
      refine ⟨40892555294009236659416825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109046814117357964425111533 40892555294009236659416825)
      ·
        refine ⟨30669416470506927494562619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40892555294009236659416825 30669416470506927494562619)
        ·
          refine ⟨46004124705760391241843929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30669416470506927494562619 46004124705760391241843929)
          ·
            refine ⟨34503093529320293431382947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46004124705760391241843929 34503093529320293431382947)
            ·
              refine ⟨51754640293980440147074421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34503093529320293431382947 51754640293980440147074421)
              ·
                refine ⟨4851997527560666263788227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51754640293980440147074421 4851997527560666263788227)
                ·
                  refine ⟨7277996291340999395682341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4851997527560666263788227 7277996291340999395682341)
                  ·
                    refine ⟨1364624304626437386690439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7277996291340999395682341 1364624304626437386690439)
                    ·
                      rfl

theorem cell23_7972789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_7972789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972789 prefixEnd_7972789 := by exact prefixLift 7972789
  have htrace : WordTrace (prefixWord ++ tailWord_7972789) baseStart_7972789 baseEnd_7972789 := by
    simpa [prefixWord, tailWord_7972789, baseEnd_7972789] using wordTrace_append hprefix tailTrace_7972789
  have hstable : (prefixWord ++ tailWord_7972789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972789).length < 2 ^ (prefixWord ++ tailWord_7972789).sum := by decide
  have hdescent : baseEnd_7972789 < baseStart_7972789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972865 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_7972865 : Nat := 118140960795 + 7972865 * 2 ^ 59
def prefixEnd_7972865 : Nat := 4983230072969 + 3 ^ 40 * 7972865 * 2
def baseEnd_7972865 : Nat := 4093911938409053862720967

theorem tailTrace_7972865 : CollatzResearch.WordTrace tailWord_7972865 prefixEnd_7972865 4093911938409053862720967 := by
  unfold tailWord_7972865
  simp only [CollatzResearch.WordTrace]
  refine ⟨290794276260679236780064049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193862850840452824520042699 290794276260679236780064049)
  ·
    refine ⟨218095707195509427585048037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290794276260679236780064049 218095707195509427585048037)
    ·
      refine ⟨40892945099158017672196507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218095707195509427585048037 40892945099158017672196507)
      ·
        refine ⟨61339417648737026508294761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40892945099158017672196507 61339417648737026508294761)
        ·
          refine ⟨46004563236552769881221071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61339417648737026508294761 46004563236552769881221071)
          ·
            refine ⟨69006844854829154821831607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46004563236552769881221071 69006844854829154821831607)
            ·
              refine ⟨103510267282243732232747411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69006844854829154821831607 103510267282243732232747411)
              ·
                refine ⟨155265400923365598349121117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103510267282243732232747411 155265400923365598349121117)
                ·
                  refine ⟨58224525346262099380920419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155265400923365598349121117 58224525346262099380920419)
                  ·
                    refine ⟨87336788019393149071380629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58224525346262099380920419 87336788019393149071380629)
                    ·
                      refine ⟨4093911938409053862720967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87336788019393149071380629 4093911938409053862720967)
                      ·
                        rfl

theorem cell23_7972865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_7972865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972865 prefixEnd_7972865 := by exact prefixLift 7972865
  have htrace : WordTrace (prefixWord ++ tailWord_7972865) baseStart_7972865 baseEnd_7972865 := by
    simpa [prefixWord, tailWord_7972865, baseEnd_7972865] using wordTrace_append hprefix tailTrace_7972865
  have hstable : (prefixWord ++ tailWord_7972865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972865).length < 2 ^ (prefixWord ++ tailWord_7972865).sum := by decide
  have hdescent : baseEnd_7972865 < baseStart_7972865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972872 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_7972872 : Nat := 118140960795 + 7972872 * 2 ^ 59
def prefixEnd_7972872 : Nat := 4983230072969 + 3 ^ 40 * 7972872 * 2
def baseEnd_7972872 : Nat := 4093915532773635335333435

theorem tailTrace_7972872 : CollatzResearch.WordTrace tailWord_7972872 prefixEnd_7972872 4093915532773635335333435 := by
  unfold tailWord_7972872
  simp only [CollatzResearch.WordTrace]
  refine ⟨145397265785826938487784435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193863021047769251317045913 145397265785826938487784435)
  ·
    refine ⟨218095898678740407731676653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145397265785826938487784435 218095898678740407731676653)
    ·
      refine ⟨81785962004527652899378745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218095898678740407731676653 81785962004527652899378745)
      ·
        refine ⟨61339471503395739674534059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81785962004527652899378745 61339471503395739674534059)
        ·
          refine ⟨92009207255093609511801089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61339471503395739674534059 92009207255093609511801089)
          ·
            refine ⟨69006905441320207133850817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92009207255093609511801089 69006905441320207133850817)
            ·
              refine ⟨51755179080990155350388113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69006905441320207133850817 51755179080990155350388113)
              ·
                refine ⟨38816384310742616512791085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51755179080990155350388113 38816384310742616512791085)
                ·
                  refine ⟨14556144116528481192296657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38816384310742616512791085 14556144116528481192296657)
                  ·
                    refine ⟨10917108087396360894222493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14556144116528481192296657 10917108087396360894222493)
                    ·
                      refine ⟨4093915532773635335333435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10917108087396360894222493 4093915532773635335333435)
                      ·
                        rfl

theorem cell23_7972872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_7972872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972872 prefixEnd_7972872 := by exact prefixLift 7972872
  have htrace : WordTrace (prefixWord ++ tailWord_7972872) baseStart_7972872 baseEnd_7972872 := by
    simpa [prefixWord, tailWord_7972872, baseEnd_7972872] using wordTrace_append hprefix tailTrace_7972872
  have hstable : (prefixWord ++ tailWord_7972872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972872).length < 2 ^ (prefixWord ++ tailWord_7972872).sum := by decide
  have hdescent : baseEnd_7972872 < baseStart_7972872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972875 : List Nat := [1, 1, 1, 1, 6, 1, 4, 8]
def baseStart_7972875 : Nat := 118140960795 + 7972875 * 2 ^ 59
def prefixEnd_7972875 : Nat := 4983230072969 + 3 ^ 40 * 7972875 * 2
def baseEnd_7972875 : Nat := 151626558267244400873923

theorem tailTrace_7972875 : CollatzResearch.WordTrace tailWord_7972875 prefixEnd_7972875 151626558267244400873923 := by
  unfold tailWord_7972875
  simp only [CollatzResearch.WordTrace]
  refine ⟨290794640990643008487928079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193863093993762005658618719 290794640990643008487928079)
  ·
    refine ⟨436191961485964512731892119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290794640990643008487928079 436191961485964512731892119)
    ·
      refine ⟨654287942228946769097838179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436191961485964512731892119 654287942228946769097838179)
      ·
        refine ⟨981431913343420153646757269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654287942228946769097838179 981431913343420153646757269)
        ·
          refine ⟨46004620937972819702191747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 981431913343420153646757269 46004620937972819702191747)
          ·
            refine ⟨69006931406959229553287621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46004620937972819702191747 69006931406959229553287621)
            ·
              refine ⟨12938799638804855541241429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69006931406959229553287621 12938799638804855541241429)
              ·
                refine ⟨151626558267244400873923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12938799638804855541241429 151626558267244400873923)
                ·
                  rfl

theorem cell23_7972875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 8].length) (baseStart_7972875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972875 prefixEnd_7972875 := by exact prefixLift 7972875
  have htrace : WordTrace (prefixWord ++ tailWord_7972875) baseStart_7972875 baseEnd_7972875 := by
    simpa [prefixWord, tailWord_7972875, baseEnd_7972875] using wordTrace_append hprefix tailTrace_7972875
  have hstable : (prefixWord ++ tailWord_7972875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972875).length < 2 ^ (prefixWord ++ tailWord_7972875).sum := by decide
  have hdescent : baseEnd_7972875 < baseStart_7972875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972903 : List Nat := [1, 1, 7, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_7972903 : Nat := 118140960795 + 7972903 * 2 ^ 59
def prefixEnd_7972903 : Nat := 4983230072969 + 3 ^ 40 * 7972903 * 2
def baseEnd_7972903 : Nat := 4093931450673924714045793

theorem tailTrace_7972903 : CollatzResearch.WordTrace tailWord_7972903 prefixEnd_7972903 4093931450673924714045793 := by
  unfold tailWord_7972903
  simp only [CollatzResearch.WordTrace]
  refine ⟨290795662234541569269947363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193863774823027712846631575 290795662234541569269947363)
  ·
    refine ⟨436193493351812353904921045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290795662234541569269947363 436193493351812353904921045)
    ·
      refine ⟨10223285000433102044646587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 436193493351812353904921045 10223285000433102044646587)
      ·
        refine ⟨15334927500649653066969881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10223285000433102044646587 15334927500649653066969881)
        ·
          refine ⟨11501195625487239800227411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15334927500649653066969881 11501195625487239800227411)
          ·
            refine ⟨17251793438230859700341117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11501195625487239800227411 17251793438230859700341117)
            ·
              refine ⟨6469422539336572387627919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17251793438230859700341117 6469422539336572387627919)
              ·
                refine ⟨9704133809004858581441879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6469422539336572387627919 9704133809004858581441879)
                ·
                  refine ⟨14556200713507287872162819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9704133809004858581441879 14556200713507287872162819)
                  ·
                    refine ⟨21834301070260931808244229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14556200713507287872162819 21834301070260931808244229)
                    ·
                      refine ⟨4093931450673924714045793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21834301070260931808244229 4093931450673924714045793)
                      ·
                        rfl

theorem cell23_7972903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_7972903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972903 prefixEnd_7972903 := by exact prefixLift 7972903
  have htrace : WordTrace (prefixWord ++ tailWord_7972903) baseStart_7972903 baseEnd_7972903 := by
    simpa [prefixWord, tailWord_7972903, baseEnd_7972903] using wordTrace_append hprefix tailTrace_7972903
  have hstable : (prefixWord ++ tailWord_7972903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972903).length < 2 ^ (prefixWord ++ tailWord_7972903).sum := by decide
  have hdescent : baseEnd_7972903 < baseStart_7972903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972915 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 5]
def baseStart_7972915 : Nat := 118140960795 + 7972915 * 2 ^ 59
def prefixEnd_7972915 : Nat := 4983230072969 + 3 ^ 40 * 7972915 * 2
def baseEnd_7972915 : Nat := 4093937612441778667095737

theorem tailTrace_7972915 : CollatzResearch.WordTrace tailWord_7972915 prefixEnd_7972915 4093937612441778667095737 := by
  unfold tailWord_7972915
  simp only [CollatzResearch.WordTrace]
  refine ⟨290796099910498095319384199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193864066606998730212922799 290796099910498095319384199)
  ·
    refine ⟨436194149865747142979076299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290796099910498095319384199 436194149865747142979076299)
    ·
      refine ⟨654291224798620714468614449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436194149865747142979076299 654291224798620714468614449)
      ·
        refine ⟨490718418598965535851460837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654291224798620714468614449 490718418598965535851460837)
        ·
          refine ⟨92009703487306037972148907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490718418598965535851460837 92009703487306037972148907)
          ·
            refine ⟨138014555230959056958223361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92009703487306037972148907 138014555230959056958223361)
            ·
              refine ⟨103510916423219292718667521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138014555230959056958223361 103510916423219292718667521)
              ·
                refine ⟨77633187317414469539000641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103510916423219292718667521 77633187317414469539000641)
                ·
                  refine ⟨58224890488060852154250481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77633187317414469539000641 58224890488060852154250481)
                  ·
                    refine ⟨43668667866045639115687861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58224890488060852154250481 43668667866045639115687861)
                    ·
                      refine ⟨4093937612441778667095737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43668667866045639115687861 4093937612441778667095737)
                      ·
                        rfl

theorem cell23_7972915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_7972915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972915 prefixEnd_7972915 := by exact prefixLift 7972915
  have htrace : WordTrace (prefixWord ++ tailWord_7972915) baseStart_7972915 baseEnd_7972915 := by
    simpa [prefixWord, tailWord_7972915, baseEnd_7972915] using wordTrace_append hprefix tailTrace_7972915
  have hstable : (prefixWord ++ tailWord_7972915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972915).length < 2 ^ (prefixWord ++ tailWord_7972915).sum := by decide
  have hdescent : baseEnd_7972915 < baseStart_7972915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972919 : List Nat := [1, 1, 3, 1, 2, 2, 3, 4, 2, 1, 3]
def baseStart_7972919 : Nat := 118140960795 + 7972919 * 2 ^ 59
def prefixEnd_7972919 : Nat := 4983230072969 + 3 ^ 40 * 7972919 * 2
def baseEnd_7972919 : Nat := 4093939666364396651445719

theorem tailTrace_7972919 : CollatzResearch.WordTrace tailWord_7972919 prefixEnd_7972919 4093939666364396651445719 := by
  unfold tailWord_7972919
  simp only [CollatzResearch.WordTrace]
  refine ⟨290796245802483604002529811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193864163868322402668353207 290796245802483604002529811)
  ·
    refine ⟨436194368703725406003794717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290796245802483604002529811 436194368703725406003794717)
    ·
      refine ⟨163572888263897027251423019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436194368703725406003794717 163572888263897027251423019)
      ·
        refine ⟨245359332395845540877134529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163572888263897027251423019 245359332395845540877134529)
        ·
          refine ⟨184019499296884155657850897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245359332395845540877134529 184019499296884155657850897)
          ·
            refine ⟨138014624472663116743388173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184019499296884155657850897 138014624472663116743388173)
            ·
              refine ⟨51755484177248668778770565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138014624472663116743388173 51755484177248668778770565)
              ·
                refine ⟨9704153283234125396019481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51755484177248668778770565 9704153283234125396019481)
                ·
                  refine ⟨7278114962425594047014611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9704153283234125396019481 7278114962425594047014611)
                  ·
                    refine ⟨10917172443638391070521917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7278114962425594047014611 10917172443638391070521917)
                    ·
                      refine ⟨4093939666364396651445719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10917172443638391070521917 4093939666364396651445719)
                      ·
                        rfl

theorem cell23_7972919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_7972919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972919 prefixEnd_7972919 := by exact prefixLift 7972919
  have htrace : WordTrace (prefixWord ++ tailWord_7972919) baseStart_7972919 baseEnd_7972919 := by
    simpa [prefixWord, tailWord_7972919, baseEnd_7972919] using wordTrace_append hprefix tailTrace_7972919
  have hstable : (prefixWord ++ tailWord_7972919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972919).length < 2 ^ (prefixWord ++ tailWord_7972919).sum := by decide
  have hdescent : baseEnd_7972919 < baseStart_7972919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972926 : List Nat := [4, 2, 1, 3, 3, 1, 1, 8]
def baseStart_7972926 : Nat := 118140960795 + 7972926 * 2 ^ 59
def prefixEnd_7972926 : Nat := 4983230072969 + 3 ^ 40 * 7972926 * 2
def baseEnd_7972926 : Nat := 151627528175147337928081

theorem tailTrace_7972926 : CollatzResearch.WordTrace tailWord_7972926 prefixEnd_7972926 151627528175147337928081 := by
  unfold tailWord_7972926
  simp only [CollatzResearch.WordTrace]
  refine ⟨36349562639182280524754329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193864334075638829465356421 36349562639182280524754329)
  ·
    refine ⟨27262171979386710393565747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36349562639182280524754329 27262171979386710393565747)
    ·
      refine ⟨40893257969080065590348621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27262171979386710393565747 40893257969080065590348621)
      ·
        refine ⟨15334971738405024596380733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40893257969080065590348621 15334971738405024596380733)
        ·
          refine ⟨5750614401901884223642775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15334971738405024596380733 5750614401901884223642775)
          ·
            refine ⟨8625921602852826335464163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5750614401901884223642775 8625921602852826335464163)
            ·
              refine ⟨12938882404279239503196245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8625921602852826335464163 12938882404279239503196245)
              ·
                refine ⟨151627528175147337928081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12938882404279239503196245 151627528175147337928081)
                ·
                  rfl

theorem cell23_7972926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_7972926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972926 prefixEnd_7972926 := by exact prefixLift 7972926
  have htrace : WordTrace (prefixWord ++ tailWord_7972926) baseStart_7972926 baseEnd_7972926 := by
    simpa [prefixWord, tailWord_7972926, baseEnd_7972926] using wordTrace_append hprefix tailTrace_7972926
  have hstable : (prefixWord ++ tailWord_7972926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972926).length < 2 ^ (prefixWord ++ tailWord_7972926).sum := by decide
  have hdescent : baseEnd_7972926 < baseStart_7972926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972970 : List Nat := [3, 1, 3, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_7972970 : Nat := 118140960795 + 7972970 * 2 ^ 59
def prefixEnd_7972970 : Nat := 4983230072969 + 3 ^ 40 * 7972970 * 2
def baseEnd_7972970 : Nat := 4093965853877775951907985

theorem tailTrace_7972970 : CollatzResearch.WordTrace tailWord_7972970 prefixEnd_7972970 4093965853877775951907985 := by
  unfold tailWord_7972970
  simp only [CollatzResearch.WordTrace]
  refine ⟨72699526481324709928159091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193865403950199226475090909 72699526481324709928159091)
  ·
    refine ⟨109049289721987064892238637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72699526481324709928159091 109049289721987064892238637)
    ·
      refine ⟨40893483645745149334589489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109049289721987064892238637 40893483645745149334589489)
      ·
        refine ⟨30670112734308862000942117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40893483645745149334589489 30670112734308862000942117)
        ·
          refine ⟨5750646137682911625176647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30670112734308862000942117 5750646137682911625176647)
          ·
            refine ⟨8625969206524367437764971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5750646137682911625176647 8625969206524367437764971)
            ·
              refine ⟨12938953809786551156647457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8625969206524367437764971 12938953809786551156647457)
              ·
                refine ⟨9704215357339913367485593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12938953809786551156647457 9704215357339913367485593)
                ·
                  refine ⟨7278161518004935025614195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9704215357339913367485593 7278161518004935025614195)
                  ·
                    refine ⟨10917242277007402538421293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7278161518004935025614195 10917242277007402538421293)
                    ·
                      refine ⟨4093965853877775951907985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10917242277007402538421293 4093965853877775951907985)
                      ·
                        rfl

theorem cell23_7972970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_7972970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972970 prefixEnd_7972970 := by exact prefixLift 7972970
  have htrace : WordTrace (prefixWord ++ tailWord_7972970) baseStart_7972970 baseEnd_7972970 := by
    simpa [prefixWord, tailWord_7972970, baseEnd_7972970] using wordTrace_append hprefix tailTrace_7972970
  have hstable : (prefixWord ++ tailWord_7972970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972970).length < 2 ^ (prefixWord ++ tailWord_7972970).sum := by decide
  have hdescent : baseEnd_7972970 < baseStart_7972970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972972 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_7972972 : Nat := 118140960795 + 7972972 * 2 ^ 59
def prefixEnd_7972972 : Nat := 4983230072969 + 3 ^ 40 * 7972972 * 2
def baseEnd_7972972 : Nat := 4093966880839084944082975

theorem tailTrace_7972972 : CollatzResearch.WordTrace tailWord_7972972 prefixEnd_7972972 4093966880839084944082975 := by
  unfold tailWord_7972972
  simp only [CollatzResearch.WordTrace]
  refine ⟨145399089435645797027104585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193865452580861062702806113 145399089435645797027104585)
  ·
    refine ⟨109049317076734347770328439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145399089435645797027104585 109049317076734347770328439)
    ·
      refine ⟨163573975615101521655492659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109049317076734347770328439 163573975615101521655492659)
      ·
        refine ⟨245360963422652282483238989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163573975615101521655492659 245360963422652282483238989)
        ·
          refine ⟨92010361283494605931214621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245360963422652282483238989 92010361283494605931214621)
          ·
            refine ⟨34503885481310477224205483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92010361283494605931214621 34503885481310477224205483)
            ·
              refine ⟨51755828221965715836308225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34503885481310477224205483 51755828221965715836308225)
              ·
                refine ⟨38816871166474286877231169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51755828221965715836308225 38816871166474286877231169)
                ·
                  refine ⟨29112653374855715157923377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38816871166474286877231169 29112653374855715157923377)
                  ·
                    refine ⟨21834490031141786368442533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29112653374855715157923377 21834490031141786368442533)
                    ·
                      refine ⟨4093966880839084944082975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21834490031141786368442533 4093966880839084944082975)
                      ·
                        rfl

theorem cell23_7972972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_7972972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972972 prefixEnd_7972972 := by exact prefixLift 7972972
  have htrace : WordTrace (prefixWord ++ tailWord_7972972) baseStart_7972972 baseEnd_7972972 := by
    simpa [prefixWord, tailWord_7972972, baseEnd_7972972] using wordTrace_append hprefix tailTrace_7972972
  have hstable : (prefixWord ++ tailWord_7972972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972972).length < 2 ^ (prefixWord ++ tailWord_7972972).sum := by decide
  have hdescent : baseEnd_7972972 < baseStart_7972972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972976 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 4, 2, 2]
def baseStart_7972976 : Nat := 118140960795 + 7972976 * 2 ^ 59
def prefixEnd_7972976 : Nat := 4983230072969 + 3 ^ 40 * 7972976 * 2
def baseEnd_7972976 : Nat := 4093968934761702928432957

theorem tailTrace_7972976 : CollatzResearch.WordTrace tailWord_7972976 prefixEnd_7972976 4093968934761702928432957 := by
  unfold tailWord_7972976
  simp only [CollatzResearch.WordTrace]
  refine ⟨145399162381638551368677391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193865549842184735158236521 145399162381638551368677391)
  ·
    refine ⟨218098743572457827053016087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145399162381638551368677391 218098743572457827053016087)
    ·
      refine ⟨327148115358686740579524131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218098743572457827053016087 327148115358686740579524131)
      ·
        refine ⟨490722173038030110869286197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327148115358686740579524131 490722173038030110869286197)
        ·
          refine ⟨46005203722315322893995581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 490722173038030110869286197 46005203722315322893995581)
          ·
            refine ⟨17251951395868246085248343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46005203722315322893995581 17251951395868246085248343)
            ·
              refine ⟨25877927093802369127872515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17251951395868246085248343 25877927093802369127872515)
              ·
                refine ⟨38816890640703553691808773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25877927093802369127872515 38816890640703553691808773)
                ·
                  refine ⟨7278166995131916317214145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38816890640703553691808773 7278166995131916317214145)
                  ·
                    refine ⟨5458625246348937237910609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7278166995131916317214145 5458625246348937237910609)
                    ·
                      refine ⟨4093968934761702928432957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458625246348937237910609 4093968934761702928432957)
                      ·
                        rfl

theorem cell23_7972976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 4, 2, 2].length) (baseStart_7972976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972976 prefixEnd_7972976 := by exact prefixLift 7972976
  have htrace : WordTrace (prefixWord ++ tailWord_7972976) baseStart_7972976 baseEnd_7972976 := by
    simpa [prefixWord, tailWord_7972976, baseEnd_7972976] using wordTrace_append hprefix tailTrace_7972976
  have hstable : (prefixWord ++ tailWord_7972976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972976).length < 2 ^ (prefixWord ++ tailWord_7972976).sum := by decide
  have hdescent : baseEnd_7972976 < baseStart_7972976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7972993 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_7972993 : Nat := 118140960795 + 7972993 * 2 ^ 59
def prefixEnd_7972993 : Nat := 4983230072969 + 3 ^ 40 * 7972993 * 2
def baseEnd_7972993 : Nat := 4093977663932829361920379

theorem tailTrace_7972993 : CollatzResearch.WordTrace tailWord_7972993 prefixEnd_7972993 4093977663932829361920379 := by
  unfold tailWord_7972993
  simp only [CollatzResearch.WordTrace]
  refine ⟨290798944804215514640723633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193865963202810343093815755 290798944804215514640723633)
  ·
    refine ⟨218099208603161635980542725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290798944804215514640723633 218099208603161635980542725)
    ·
      refine ⟨40893601613092806746351761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218099208603161635980542725 40893601613092806746351761)
      ·
        refine ⟨30670201209819605059763821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40893601613092806746351761 30670201209819605059763821)
        ·
          refine ⟨11501325453682351897411433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30670201209819605059763821 11501325453682351897411433)
          ·
            refine ⟨8625994090261763923058575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11501325453682351897411433 8625994090261763923058575)
            ·
              refine ⟨12938991135392645884587863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8625994090261763923058575 12938991135392645884587863)
              ·
                refine ⟨19408486703088968826881795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12938991135392645884587863 19408486703088968826881795)
                ·
                  refine ⟨29112730054633453240322693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19408486703088968826881795 29112730054633453240322693)
                  ·
                    refine ⟨5458636885243772482560505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29112730054633453240322693 5458636885243772482560505)
                    ·
                      refine ⟨4093977663932829361920379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458636885243772482560505 4093977663932829361920379)
                      ·
                        rfl

theorem cell23_7972993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_7972993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7972993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7972993 prefixEnd_7972993 := by exact prefixLift 7972993
  have htrace : WordTrace (prefixWord ++ tailWord_7972993) baseStart_7972993 baseEnd_7972993 := by
    simpa [prefixWord, tailWord_7972993, baseEnd_7972993] using wordTrace_append hprefix tailTrace_7972993
  have hstable : (prefixWord ++ tailWord_7972993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7972993).length < 2 ^ (prefixWord ++ tailWord_7972993).sum := by decide
  have hdescent : baseEnd_7972993 < baseStart_7972993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7972993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973044 : List Nat := [2, 5, 3, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_7973044 : Nat := 118140960795 + 7973044 * 2 ^ 59
def prefixEnd_7973044 : Nat := 4983230072969 + 3 ^ 40 * 7973044 * 2
def baseEnd_7973044 : Nat := 4094003851446208662382645

theorem tailTrace_7973044 : CollatzResearch.WordTrace tailWord_7973044 prefixEnd_7973044 4094003851446208662382645 := by
  unfold tailWord_7973044
  simp only [CollatzResearch.WordTrace]
  refine ⟨145400402463515375175415093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193867203284687166900553457 145400402463515375175415093)
  ·
    refine ⟨13631287730954566422695165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145400402463515375175415093 13631287730954566422695165)
    ·
      refine ⟨5111732899107962408510687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13631287730954566422695165 5111732899107962408510687)
      ·
        refine ⟨7667599348661943612766031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5111732899107962408510687 7667599348661943612766031)
        ·
          refine ⟨11501399022992915419149047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7667599348661943612766031 11501399022992915419149047)
          ·
            refine ⟨17252098534489373128723571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11501399022992915419149047 17252098534489373128723571)
            ·
              refine ⟨25878147801734059693085357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17252098534489373128723571 25878147801734059693085357)
              ·
                refine ⟨9704305425650272384907009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25878147801734059693085357 9704305425650272384907009)
                ·
                  refine ⟨7278229069237704288680257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9704305425650272384907009 7278229069237704288680257)
                  ·
                    refine ⟨5458671801928278216510193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7278229069237704288680257 5458671801928278216510193)
                    ·
                      refine ⟨4094003851446208662382645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458671801928278216510193 4094003851446208662382645)
                      ·
                        rfl

theorem cell23_7973044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_7973044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973044 prefixEnd_7973044 := by exact prefixLift 7973044
  have htrace : WordTrace (prefixWord ++ tailWord_7973044) baseStart_7973044 baseEnd_7973044 := by
    simpa [prefixWord, tailWord_7973044, baseEnd_7973044] using wordTrace_append hprefix tailTrace_7973044
  have hstable : (prefixWord ++ tailWord_7973044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973044).length < 2 ^ (prefixWord ++ tailWord_7973044).sum := by decide
  have hdescent : baseEnd_7973044 < baseStart_7973044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973049 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 1, 6, 2]
def baseStart_7973049 : Nat := 118140960795 + 7973049 * 2 ^ 59
def prefixEnd_7973049 : Nat := 4983230072969 + 3 ^ 40 * 7973049 * 2
def baseEnd_7973049 : Nat := 4094006418849481142820121

theorem tailTrace_7973049 : CollatzResearch.WordTrace tailWord_7973049 prefixEnd_7973049 4094006418849481142820121 := by
  unfold tailWord_7973049
  simp only [CollatzResearch.WordTrace]
  refine ⟨290800987292012636204762201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193867324861341757469841467 290800987292012636204762201)
  ·
    refine ⟨218100740469009477153571651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290800987292012636204762201 218100740469009477153571651)
    ·
      refine ⟨327151110703514215730357477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218100740469009477153571651 327151110703514215730357477)
      ·
        refine ⟨61340833256908915449442027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327151110703514215730357477 61340833256908915449442027)
        ·
          refine ⟨92011249885363373174163041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61340833256908915449442027 92011249885363373174163041)
          ·
            refine ⟨69008437414022529880622281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92011249885363373174163041 69008437414022529880622281)
            ·
              refine ⟨51756328060516897410466711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69008437414022529880622281 51756328060516897410466711)
              ·
                refine ⟨77634492090775346115700067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51756328060516897410466711 77634492090775346115700067)
                ·
                  refine ⟨116451738136163019173550101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77634492090775346115700067 116451738136163019173550101)
                  ·
                    refine ⟨5458675225132641523760161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116451738136163019173550101 5458675225132641523760161)
                    ·
                      refine ⟨4094006418849481142820121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458675225132641523760161 4094006418849481142820121)
                      ·
                        rfl

theorem cell23_7973049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_7973049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973049 prefixEnd_7973049 := by exact prefixLift 7973049
  have htrace : WordTrace (prefixWord ++ tailWord_7973049) baseStart_7973049 baseEnd_7973049 := by
    simpa [prefixWord, tailWord_7973049, baseEnd_7973049] using wordTrace_append hprefix tailTrace_7973049
  have hstable : (prefixWord ++ tailWord_7973049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973049).length < 2 ^ (prefixWord ++ tailWord_7973049).sum := by decide
  have hdescent : baseEnd_7973049 < baseStart_7973049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973089 : List Nat := [1, 2, 3, 1, 3, 1, 4, 2, 6]
def baseStart_7973089 : Nat := 118140960795 + 7973089 * 2 ^ 59
def prefixEnd_7973089 : Nat := 4983230072969 + 3 ^ 40 * 7973089 * 2
def baseEnd_7973089 : Nat := 454891884230628998479993

theorem tailTrace_7973089 : CollatzResearch.WordTrace tailWord_7973089 prefixEnd_7973089 454891884230628998479993 := by
  unfold tailWord_7973089
  simp only [CollatzResearch.WordTrace]
  refine ⟨290802446211867723036218321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193868297474578482024145547 290802446211867723036218321)
  ·
    refine ⟨218101834658900792277163741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290802446211867723036218321 218101834658900792277163741)
    ·
      refine ⟨81788187997087797103936403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218101834658900792277163741 81788187997087797103936403)
      ·
        refine ⟨122682281995631695655904605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81788187997087797103936403 122682281995631695655904605)
        ·
          refine ⟨46005855748361885870964227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122682281995631695655904605 46005855748361885870964227)
          ·
            refine ⟨69008783622542828806446341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46005855748361885870964227 69008783622542828806446341)
            ·
              refine ⟨12939146929226780401208689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69008783622542828806446341 12939146929226780401208689)
              ·
                refine ⟨9704360196920085300906517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12939146929226780401208689 9704360196920085300906517)
                ·
                  refine ⟨454891884230628998479993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9704360196920085300906517 454891884230628998479993)
                  ·
                    rfl

theorem cell23_7973089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 6].length) (baseStart_7973089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973089 prefixEnd_7973089 := by exact prefixLift 7973089
  have htrace : WordTrace (prefixWord ++ tailWord_7973089) baseStart_7973089 baseEnd_7973089 := by
    simpa [prefixWord, tailWord_7973089, baseEnd_7973089] using wordTrace_append hprefix tailTrace_7973089
  have hstable : (prefixWord ++ tailWord_7973089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973089).length < 2 ^ (prefixWord ++ tailWord_7973089).sum := by decide
  have hdescent : baseEnd_7973089 < baseStart_7973089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973092 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_7973092 : Nat := 118140960795 + 7973092 * 2 ^ 59
def prefixEnd_7973092 : Nat := 4983230072969 + 3 ^ 40 * 7973092 * 2
def baseEnd_7973092 : Nat := 4094028498517624474582423

theorem tailTrace_7973092 : CollatzResearch.WordTrace tailWord_7973092 prefixEnd_7973092 4094028498517624474582423 := by
  unfold tailWord_7973092
  simp only [CollatzResearch.WordTrace]
  refine ⟨145401277815428427274288765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193868370420571236365718353 145401277815428427274288765)
  ·
    refine ⟨54525479180785660227858287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145401277815428427274288765 54525479180785660227858287)
    ·
      refine ⟨81788218771178490341787431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54525479180785660227858287 81788218771178490341787431)
      ·
        refine ⟨122682328156767735512681147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81788218771178490341787431 122682328156767735512681147)
        ·
          refine ⟨184023492235151603269021721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122682328156767735512681147 184023492235151603269021721)
          ·
            refine ⟨138017619176363702451766291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184023492235151603269021721 138017619176363702451766291)
            ·
              refine ⟨207026428764545553677649437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138017619176363702451766291 207026428764545553677649437)
              ·
                refine ⟨77634910786704582629118539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207026428764545553677649437 77634910786704582629118539)
                ·
                  refine ⟨116452366180056873943677809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77634910786704582629118539 116452366180056873943677809)
                  ·
                    refine ⟨87339274635042655457758357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116452366180056873943677809 87339274635042655457758357)
                    ·
                      refine ⟨4094028498517624474582423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87339274635042655457758357 4094028498517624474582423)
                      ·
                        rfl

theorem cell23_7973092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_7973092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973092 prefixEnd_7973092 := by exact prefixLift 7973092
  have htrace : WordTrace (prefixWord ++ tailWord_7973092) baseStart_7973092 baseEnd_7973092 := by
    simpa [prefixWord, tailWord_7973092, baseEnd_7973092] using wordTrace_append hprefix tailTrace_7973092
  have hstable : (prefixWord ++ tailWord_7973092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973092).length < 2 ^ (prefixWord ++ tailWord_7973092).sum := by decide
  have hdescent : baseEnd_7973092 < baseStart_7973092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973093 : List Nat := [1, 3, 1, 4, 2, 2, 1, 4, 1, 4]
def baseStart_7973093 : Nat := 118140960795 + 7973093 * 2 ^ 59
def prefixEnd_7973093 : Nat := 4983230072969 + 3 ^ 40 * 7973093 * 2
def baseEnd_7973093 : Nat := 1364676337332759656889973

theorem tailTrace_7973093 : CollatzResearch.WordTrace tailWord_7973093 prefixEnd_7973093 1364676337332759656889973 := by
  unfold tailWord_7973093
  simp only [CollatzResearch.WordTrace]
  refine ⟨290802592103853231719363933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193868394735902154479575955 290802592103853231719363933)
  ·
    refine ⟨109050972038944961894761475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290802592103853231719363933 109050972038944961894761475)
    ·
      refine ⟨163576458058417442842142213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109050972038944961894761475 163576458058417442842142213)
      ·
        refine ⟨30670585885953270532901665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163576458058417442842142213 30670585885953270532901665)
        ·
          refine ⟨23002939414464952899676249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30670585885953270532901665 23002939414464952899676249)
          ·
            refine ⟨17252204560848714674757187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23002939414464952899676249 17252204560848714674757187)
            ·
              refine ⟨25878306841273072012135781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17252204560848714674757187 25878306841273072012135781)
              ·
                refine ⟨4852182532738701002275459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25878306841273072012135781 4852182532738701002275459)
                ·
                  refine ⟨7278273799108051503413189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852182532738701002275459 7278273799108051503413189)
                  ·
                    refine ⟨1364676337332759656889973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7278273799108051503413189 1364676337332759656889973)
                    ·
                      rfl

theorem cell23_7973093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_7973093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973093 prefixEnd_7973093 := by exact prefixLift 7973093
  have htrace : WordTrace (prefixWord ++ tailWord_7973093) baseStart_7973093 baseEnd_7973093 := by
    simpa [prefixWord, tailWord_7973093, baseEnd_7973093] using wordTrace_append hprefix tailTrace_7973093
  have hstable : (prefixWord ++ tailWord_7973093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973093).length < 2 ^ (prefixWord ++ tailWord_7973093).sum := by decide
  have hdescent : baseEnd_7973093 < baseStart_7973093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973116 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_7973116 : Nat := 118140960795 + 7973116 * 2 ^ 59
def prefixEnd_7973116 : Nat := 4983230072969 + 3 ^ 40 * 7973116 * 2
def baseEnd_7973116 : Nat := 4094040822053332380682313

theorem tailTrace_7973116 : CollatzResearch.WordTrace tailWord_7973116 prefixEnd_7973116 4094040822053332380682313 := by
  unfold tailWord_7973116
  simp only [CollatzResearch.WordTrace]
  refine ⟨145401715491384953323725601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193868953988513271098300801 145401715491384953323725601)
  ·
    refine ⟨109051286618538714992794201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145401715491384953323725601 109051286618538714992794201)
    ·
      refine ⟨81788464963904036244595651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109051286618538714992794201 81788464963904036244595651)
      ·
        refine ⟨122682697445856054366893477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81788464963904036244595651 122682697445856054366893477)
        ·
          refine ⟨23003005771098010193792527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122682697445856054366893477 23003005771098010193792527)
          ·
            refine ⟨34504508656647015290688791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23003005771098010193792527 34504508656647015290688791)
            ·
              refine ⟨51756762984970522936033187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34504508656647015290688791 51756762984970522936033187)
              ·
                refine ⟨77635144477455784404049781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51756762984970522936033187 77635144477455784404049781)
                ·
                  refine ⟨7278294794761479787879667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77635144477455784404049781 7278294794761479787879667)
                  ·
                    refine ⟨10917442192142219681819501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7278294794761479787879667 10917442192142219681819501)
                    ·
                      refine ⟨4094040822053332380682313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10917442192142219681819501 4094040822053332380682313)
                      ·
                        rfl

theorem cell23_7973116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_7973116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973116 prefixEnd_7973116 := by exact prefixLift 7973116
  have htrace : WordTrace (prefixWord ++ tailWord_7973116) baseStart_7973116 baseEnd_7973116 := by
    simpa [prefixWord, tailWord_7973116, baseEnd_7973116] using wordTrace_append hprefix tailTrace_7973116
  have hstable : (prefixWord ++ tailWord_7973116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973116).length < 2 ^ (prefixWord ++ tailWord_7973116).sum := by decide
  have hdescent : baseEnd_7973116 < baseStart_7973116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973119 : List Nat := [1, 1, 2, 2, 1, 4, 2, 4, 1, 5]
def baseStart_7973119 : Nat := 118140960795 + 7973119 * 2 ^ 59
def prefixEnd_7973119 : Nat := 4983230072969 + 3 ^ 40 * 7973119 * 2
def baseEnd_7973119 : Nat := 1364680787498431956314933

theorem tailTrace_7973119 : CollatzResearch.WordTrace tailWord_7973119 prefixEnd_7973119 1364680787498431956314933 := by
  unfold tailWord_7973119
  simp only [CollatzResearch.WordTrace]
  refine ⟨290803540401759038159810411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193869026934506025439873607 290803540401759038159810411)
  ·
    refine ⟨436205310602638557239715617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290803540401759038159810411 436205310602638557239715617)
    ·
      refine ⟨327153982951978917929786713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436205310602638557239715617 327153982951978917929786713)
      ·
        refine ⟨245365487213984188447340035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327153982951978917929786713 245365487213984188447340035)
        ·
          refine ⟨368048230820976282671010053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245365487213984188447340035 368048230820976282671010053)
          ·
            refine ⟨69009043278933053000814385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 368048230820976282671010053 69009043278933053000814385)
            ·
              refine ⟨51756782459199789750610789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69009043278933053000814385 51756782459199789750610789)
              ·
                refine ⟨9704396711099960578239523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51756782459199789750610789 9704396711099960578239523)
                ·
                  refine ⟨14556595066649940867359285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9704396711099960578239523 14556595066649940867359285)
                  ·
                    refine ⟨1364680787498431956314933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14556595066649940867359285 1364680787498431956314933)
                    ·
                      rfl

theorem cell23_7973119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 5].length) (baseStart_7973119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973119 prefixEnd_7973119 := by exact prefixLift 7973119
  have htrace : WordTrace (prefixWord ++ tailWord_7973119) baseStart_7973119 baseEnd_7973119 := by
    simpa [prefixWord, tailWord_7973119, baseEnd_7973119] using wordTrace_append hprefix tailTrace_7973119
  have hstable : (prefixWord ++ tailWord_7973119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973119).length < 2 ^ (prefixWord ++ tailWord_7973119).sum := by decide
  have hdescent : baseEnd_7973119 < baseStart_7973119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973139 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 1, 8, 2]
def baseStart_7973139 : Nat := 118140960795 + 7973139 * 2 ^ 59
def prefixEnd_7973139 : Nat := 4983230072969 + 3 ^ 40 * 7973139 * 2
def baseEnd_7973139 : Nat := 4094052632108385790694707

theorem tailTrace_7973139 : CollatzResearch.WordTrace tailWord_7973139 prefixEnd_7973139 4094052632108385790694707 := by
  unfold tailWord_7973139
  simp only [CollatzResearch.WordTrace]
  refine ⟨290804269861686581575538471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193869513241124387717025647 290804269861686581575538471)
  ·
    refine ⟨436206404792529872363307707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290804269861686581575538471 436206404792529872363307707)
    ·
      refine ⟨654309607188794808544961561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436206404792529872363307707 654309607188794808544961561)
      ·
        refine ⟨490732205391596106408721171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654309607188794808544961561 490732205391596106408721171)
        ·
          refine ⟨736098308087394159613081757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490732205391596106408721171 736098308087394159613081757)
          ·
            refine ⟨276036865532772809854905659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736098308087394159613081757 276036865532772809854905659)
            ·
              refine ⟨414055298299159214782358489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276036865532772809854905659 414055298299159214782358489)
              ·
                refine ⟨310541473724369411086768867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414055298299159214782358489 310541473724369411086768867)
                ·
                  refine ⟨465812210586554116630153301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310541473724369411086768867 465812210586554116630153301)
                  ·
                    refine ⟨5458736842811181054259609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 465812210586554116630153301 5458736842811181054259609)
                    ·
                      refine ⟨4094052632108385790694707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458736842811181054259609 4094052632108385790694707)
                      ·
                        rfl

theorem cell23_7973139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 8, 2].length) (baseStart_7973139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973139 prefixEnd_7973139 := by exact prefixLift 7973139
  have htrace : WordTrace (prefixWord ++ tailWord_7973139) baseStart_7973139 baseEnd_7973139 := by
    simpa [prefixWord, tailWord_7973139, baseEnd_7973139] using wordTrace_append hprefix tailTrace_7973139
  have hstable : (prefixWord ++ tailWord_7973139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973139).length < 2 ^ (prefixWord ++ tailWord_7973139).sum := by decide
  have hdescent : baseEnd_7973139 < baseStart_7973139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973150 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_7973150 : Nat := 118140960795 + 7973150 * 2 ^ 59
def prefixEnd_7973150 : Nat := 4983230072969 + 3 ^ 40 * 7973150 * 2
def baseEnd_7973150 : Nat := 4094058280395585247657157

theorem tailTrace_7973150 : CollatzResearch.WordTrace tailWord_7973150 prefixEnd_7973150 4094058280395585247657157 := by
  unfold tailWord_7973150
  simp only [CollatzResearch.WordTrace]
  refine ⟨36350583883080841306773613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193869780709764486969459269 36350583883080841306773613)
  ·
    refine ⟨13631468956155315490040105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36350583883080841306773613 13631468956155315490040105)
    ·
      refine ⟨10223601717116486617530079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13631468956155315490040105 10223601717116486617530079)
      ·
        refine ⟨15335402575674729926295119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10223601717116486617530079 15335402575674729926295119)
        ·
          refine ⟨23003103863512094889442679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15335402575674729926295119 23003103863512094889442679)
          ·
            refine ⟨34504655795268142334164019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23003103863512094889442679 34504655795268142334164019)
            ·
              refine ⟨51756983692902213501246029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34504655795268142334164019 51756983692902213501246029)
              ·
                refine ⟨19408868884838330062967261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51756983692902213501246029 19408868884838330062967261)
                ·
                  refine ⟨7278325831814373773612723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19408868884838330062967261 7278325831814373773612723)
                  ·
                    refine ⟨10917488747721560660419085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7278325831814373773612723 10917488747721560660419085)
                    ·
                      refine ⟨4094058280395585247657157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10917488747721560660419085 4094058280395585247657157)
                      ·
                        rfl

theorem cell23_7973150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_7973150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973150 prefixEnd_7973150 := by exact prefixLift 7973150
  have htrace : WordTrace (prefixWord ++ tailWord_7973150) baseStart_7973150 baseEnd_7973150 := by
    simpa [prefixWord, tailWord_7973150, baseEnd_7973150] using wordTrace_append hprefix tailTrace_7973150
  have hstable : (prefixWord ++ tailWord_7973150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973150).length < 2 ^ (prefixWord ++ tailWord_7973150).sum := by decide
  have hdescent : baseEnd_7973150 < baseStart_7973150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973173 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_7973173 : Nat := 118140960795 + 7973173 * 2 ^ 59
def prefixEnd_7973173 : Nat := 4983230072969 + 3 ^ 40 * 7973173 * 2
def baseEnd_7973173 : Nat := 4094070090450638657669551

theorem tailTrace_7973173 : CollatzResearch.WordTrace tailWord_7973173 prefixEnd_7973173 4094070090450638657669551 := by
  unfold tailWord_7973173
  simp only [CollatzResearch.WordTrace]
  refine ⟨290805509943563405382276173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193870339962375603588184115 290805509943563405382276173)
  ·
    refine ⟨109052066228836277018353565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290805509943563405382276173 109052066228836277018353565)
    ·
      refine ⟨40894524835813603881882587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109052066228836277018353565 40894524835813603881882587)
      ·
        refine ⟨61341787253720405822823881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40894524835813603881882587 61341787253720405822823881)
        ·
          refine ⟨46006340440290304367117911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61341787253720405822823881 46006340440290304367117911)
          ·
            refine ⟨69009510660435456550676867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46006340440290304367117911 69009510660435456550676867)
            ·
              refine ⟨103514265990653184826015301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69009510660435456550676867 103514265990653184826015301)
              ·
                refine ⟨19408924873247472154877869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103514265990653184826015301 19408924873247472154877869)
                ·
                  refine ⟨7278346827467802058079201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19408924873247472154877869 7278346827467802058079201)
                  ·
                    refine ⟨5458760120600851543559401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7278346827467802058079201 5458760120600851543559401)
                    ·
                      refine ⟨4094070090450638657669551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458760120600851543559401 4094070090450638657669551)
                      ·
                        rfl

theorem cell23_7973173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_7973173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973173 prefixEnd_7973173 := by exact prefixLift 7973173
  have htrace : WordTrace (prefixWord ++ tailWord_7973173) baseStart_7973173 baseEnd_7973173 := by
    simpa [prefixWord, tailWord_7973173, baseEnd_7973173] using wordTrace_append hprefix tailTrace_7973173
  have hstable : (prefixWord ++ tailWord_7973173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973173).length < 2 ^ (prefixWord ++ tailWord_7973173).sum := by decide
  have hdescent : baseEnd_7973173 < baseStart_7973173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973176 : List Nat := [2, 1, 2, 1, 3, 1, 3, 4, 1, 2, 3]
def baseStart_7973176 : Nat := 118140960795 + 7973176 * 2 ^ 59
def prefixEnd_7973176 : Nat := 4983230072969 + 3 ^ 40 * 7973176 * 2
def baseEnd_7973176 : Nat := 4094071630892602145932037

theorem tailTrace_7973176 : CollatzResearch.WordTrace tailWord_7973176 prefixEnd_7973176 4094071630892602145932037 := by
  unfold tailWord_7973176
  simp only [CollatzResearch.WordTrace]
  refine ⟨145402809681276268447317691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193870412908368357929756921 145402809681276268447317691)
  ·
    refine ⟨218104214521914402670976537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145402809681276268447317691 218104214521914402670976537)
    ·
      refine ⟨163578160891435802003232403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218104214521914402670976537 163578160891435802003232403)
      ·
        refine ⟨245367241337153703004848605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163578160891435802003232403 245367241337153703004848605)
        ·
          refine ⟨92012715501432638626818227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245367241337153703004848605 92012715501432638626818227)
          ·
            refine ⟨138019073252148957940227341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92012715501432638626818227 138019073252148957940227341)
            ·
              refine ⟨51757152469555859227585253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138019073252148957940227341 51757152469555859227585253)
              ·
                refine ⟨9704466088041723605172235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51757152469555859227585253 9704466088041723605172235)
                ·
                  refine ⟨14556699132062585407758353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9704466088041723605172235 14556699132062585407758353)
                  ·
                    refine ⟨10917524349046939055818765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14556699132062585407758353 10917524349046939055818765)
                    ·
                      refine ⟨4094071630892602145932037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10917524349046939055818765 4094071630892602145932037)
                      ·
                        rfl

theorem cell23_7973176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_7973176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973176 prefixEnd_7973176 := by exact prefixLift 7973176
  have htrace : WordTrace (prefixWord ++ tailWord_7973176) baseStart_7973176 baseEnd_7973176 := by
    simpa [prefixWord, tailWord_7973176, baseEnd_7973176] using wordTrace_append hprefix tailTrace_7973176
  have hstable : (prefixWord ++ tailWord_7973176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973176).length < 2 ^ (prefixWord ++ tailWord_7973176).sum := by decide
  have hdescent : baseEnd_7973176 < baseStart_7973176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973207 : List Nat := [1, 1, 3, 2, 3, 1, 5, 2, 1, 2, 2]
def baseStart_7973207 : Nat := 118140960795 + 7973207 * 2 ^ 59
def prefixEnd_7973207 : Nat := 4983230072969 + 3 ^ 40 * 7973207 * 2
def baseEnd_7973207 : Nat := 4094087548792891524644395

theorem tailTrace_7973207 : CollatzResearch.WordTrace tailWord_7973207 prefixEnd_7973207 4094087548792891524644395 := by
  unfold tailWord_7973207
  simp only [CollatzResearch.WordTrace]
  refine ⟨290806750025440229189013875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193871166683626819459342583 290806750025440229189013875)
  ·
    refine ⟨436210125038160343783520813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290806750025440229189013875 436210125038160343783520813)
    ·
      refine ⟨163578796889310128918820305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436210125038160343783520813 163578796889310128918820305)
      ·
        refine ⟨122684097666982596689115229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163578796889310128918820305 122684097666982596689115229)
        ·
          refine ⟨46006536625118473758418211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122684097666982596689115229 46006536625118473758418211)
          ·
            refine ⟨69009804937677710637627317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46006536625118473758418211 69009804937677710637627317)
            ·
              refine ⟨6469669212907285372277561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69009804937677710637627317 6469669212907285372277561)
              ·
                refine ⟨4852251909680464029208171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6469669212907285372277561 4852251909680464029208171)
                ·
                  refine ⟨7278377864520696043812257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852251909680464029208171 7278377864520696043812257)
                  ·
                    refine ⟨5458783398390522032859193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7278377864520696043812257 5458783398390522032859193)
                    ·
                      refine ⟨4094087548792891524644395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458783398390522032859193 4094087548792891524644395)
                      ·
                        rfl

theorem cell23_7973207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_7973207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973207 prefixEnd_7973207 := by exact prefixLift 7973207
  have htrace : WordTrace (prefixWord ++ tailWord_7973207) baseStart_7973207 baseEnd_7973207 := by
    simpa [prefixWord, tailWord_7973207, baseEnd_7973207] using wordTrace_append hprefix tailTrace_7973207
  have hstable : (prefixWord ++ tailWord_7973207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973207).length < 2 ^ (prefixWord ++ tailWord_7973207).sum := by decide
  have hdescent : baseEnd_7973207 < baseStart_7973207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973258 : List Nat := [3, 1, 2, 5, 2, 1, 2, 2, 1, 2, 2]
def baseStart_7973258 : Nat := 118140960795 + 7973258 * 2 ^ 59
def prefixEnd_7973258 : Nat := 4983230072969 + 3 ^ 40 * 7973258 * 2
def baseEnd_7973258 : Nat := 4094113736306270825106661

theorem tailTrace_7973258 : CollatzResearch.WordTrace tailWord_7973258 prefixEnd_7973258 4094113736306270825106661 := by
  unfold tailWord_7973258
  simp only [CollatzResearch.WordTrace]
  refine ⟨72702152537063866224780107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193872406765503643266080285 72702152537063866224780107)
  ·
    refine ⟨109053228805595799337170161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72702152537063866224780107 109053228805595799337170161)
    ·
      refine ⟨81789921604196849502877621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109053228805595799337170161 81789921604196849502877621)
      ·
        refine ⟨7667805150393454640894777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81789921604196849502877621 7667805150393454640894777)
        ·
          refine ⟨5750853862795090980671083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7667805150393454640894777 5750853862795090980671083)
          ·
            refine ⟨8626280794192636471006625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5750853862795090980671083 8626280794192636471006625)
            ·
              refine ⟨6469710595644477353254969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8626280794192636471006625 6469710595644477353254969)
              ·
                refine ⟨4852282946733358014941227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6469710595644477353254969 4852282946733358014941227)
                ·
                  refine ⟨7278424420100037022411841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852282946733358014941227 7278424420100037022411841)
                  ·
                    refine ⟨5458818315075027766808881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7278424420100037022411841 5458818315075027766808881)
                    ·
                      refine ⟨4094113736306270825106661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458818315075027766808881 4094113736306270825106661)
                      ·
                        rfl

theorem cell23_7973258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_7973258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973258 prefixEnd_7973258 := by exact prefixLift 7973258
  have htrace : WordTrace (prefixWord ++ tailWord_7973258) baseStart_7973258 baseEnd_7973258 := by
    simpa [prefixWord, tailWord_7973258, baseEnd_7973258] using wordTrace_append hprefix tailTrace_7973258
  have hstable : (prefixWord ++ tailWord_7973258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973258).length < 2 ^ (prefixWord ++ tailWord_7973258).sum := by decide
  have hdescent : baseEnd_7973258 < baseStart_7973258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973269 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 7]
def baseStart_7973269 : Nat := 118140960795 + 7973269 * 2 ^ 59
def prefixEnd_7973269 : Nat := 4983230072969 + 3 ^ 40 * 7973269 * 2
def baseEnd_7973269 : Nat := 454902153843718920229901

theorem tailTrace_7973269 : CollatzResearch.WordTrace tailWord_7973269 prefixEnd_7973269 454902153843718920229901 := by
  unfold tailWord_7973269
  simp only [CollatzResearch.WordTrace]
  refine ⟨290809011351215613777770861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193872674234143742518513907 290809011351215613777770861)
  ·
    refine ⟨109053379256705855166664073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290809011351215613777770861 109053379256705855166664073)
    ·
      refine ⟨81790034442529391374998055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109053379256705855166664073 81790034442529391374998055)
      ·
        refine ⟨122685051663794087062497083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81790034442529391374998055 122685051663794087062497083)
        ·
          refine ⟨184027577495691130593745625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122685051663794087062497083 184027577495691130593745625)
          ·
            refine ⟨138020683121768347945309219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184027577495691130593745625 138020683121768347945309219)
            ·
              refine ⟨207031024682652521917963829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138020683121768347945309219 207031024682652521917963829)
              ·
                refine ⟨19409158563998673929809109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207031024682652521917963829 19409158563998673929809109)
                ·
                  refine ⟨454902153843718920229901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19409158563998673929809109 454902153843718920229901)
                  ·
                    rfl

theorem cell23_7973269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_7973269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973269 prefixEnd_7973269 := by exact prefixLift 7973269
  have htrace : WordTrace (prefixWord ++ tailWord_7973269) baseStart_7973269 baseEnd_7973269 := by
    simpa [prefixWord, tailWord_7973269, baseEnd_7973269] using wordTrace_append hprefix tailTrace_7973269
  have hstable : (prefixWord ++ tailWord_7973269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973269).length < 2 ^ (prefixWord ++ tailWord_7973269).sum := by decide
  have hdescent : baseEnd_7973269 < baseStart_7973269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973280 : List Nat := [2, 1, 1, 4, 1, 3, 2, 3, 2, 2, 2]
def baseStart_7973280 : Nat := 118140960795 + 7973280 * 2 ^ 59
def prefixEnd_7973280 : Nat := 4983230072969 + 3 ^ 40 * 7973280 * 2
def baseEnd_7973280 : Nat := 4094125032880669739031559

theorem tailTrace_7973280 : CollatzResearch.WordTrace tailWord_7973280 prefixEnd_7973280 4094125032880669739031559 := by
  unfold tailWord_7973280
  simp only [CollatzResearch.WordTrace]
  refine ⟨145404706277087881328210647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193872941702783841770947529 145404706277087881328210647)
  ·
    refine ⟨218107059415631821992315971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145404706277087881328210647 218107059415631821992315971)
    ·
      refine ⟨327160589123447732988473957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218107059415631821992315971 327160589123447732988473957)
      ·
        refine ⟨61342610460646449935338867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327160589123447732988473957 61342610460646449935338867)
        ·
          refine ⟨92013915690969674903008301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61342610460646449935338867 92013915690969674903008301)
          ·
            refine ⟨34505218384113628088628113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92013915690969674903008301 34505218384113628088628113)
            ·
              refine ⟨25878913788085221066471085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34505218384113628088628113 25878913788085221066471085)
              ·
                refine ⟨9704592670531957899926657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25878913788085221066471085 9704592670531957899926657)
                ·
                  refine ⟨7278444502898968424944993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9704592670531957899926657 7278444502898968424944993)
                  ·
                    refine ⟨5458833377174226318708745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7278444502898968424944993 5458833377174226318708745)
                    ·
                      refine ⟨4094125032880669739031559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458833377174226318708745 4094125032880669739031559)
                      ·
                        rfl

theorem cell23_7973280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_7973280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973280 prefixEnd_7973280 := by exact prefixLift 7973280
  have htrace : WordTrace (prefixWord ++ tailWord_7973280) baseStart_7973280 baseEnd_7973280 := by
    simpa [prefixWord, tailWord_7973280, baseEnd_7973280] using wordTrace_append hprefix tailTrace_7973280
  have hstable : (prefixWord ++ tailWord_7973280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973280).length < 2 ^ (prefixWord ++ tailWord_7973280).sum := by decide
  have hdescent : baseEnd_7973280 < baseStart_7973280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973303 : List Nat := [1, 1, 3, 1, 3, 4, 2, 3, 5]
def baseStart_7973303 : Nat := 118140960795 + 7973303 * 2 ^ 59
def prefixEnd_7973303 : Nat := 4983230072969 + 3 ^ 40 * 7973303 * 2
def baseEnd_7973303 : Nat := 454904093659524794338217

theorem tailTrace_7973303 : CollatzResearch.WordTrace tailWord_7973303 prefixEnd_7973303 454904093659524794338217 := by
  unfold tailWord_7973303
  simp only [CollatzResearch.WordTrace]
  refine ⟨290810251433092437584508563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193873500955394958389672375 290810251433092437584508563)
  ·
    refine ⟨436215377149638656376762845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290810251433092437584508563 436215377149638656376762845)
    ·
      refine ⟨163580766431114496141286067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436215377149638656376762845 163580766431114496141286067)
      ·
        refine ⟨245371149646671744211929101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163580766431114496141286067 245371149646671744211929101)
        ·
          refine ⟨92014181117501904079473413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245371149646671744211929101 92014181117501904079473413)
          ·
            refine ⟨17252658959531607014901265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92014181117501904079473413 17252658959531607014901265)
            ·
              refine ⟨12939494219648705261175949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17252658959531607014901265 12939494219648705261175949)
              ·
                refine ⟨4852310332368264472940981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12939494219648705261175949 4852310332368264472940981)
                ·
                  refine ⟨454904093659524794338217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4852310332368264472940981 454904093659524794338217)
                  ·
                    rfl

theorem cell23_7973303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 5].length) (baseStart_7973303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973303 prefixEnd_7973303 := by exact prefixLift 7973303
  have htrace : WordTrace (prefixWord ++ tailWord_7973303) baseStart_7973303 baseEnd_7973303 := by
    simpa [prefixWord, tailWord_7973303, baseEnd_7973303] using wordTrace_append hprefix tailTrace_7973303
  have hstable : (prefixWord ++ tailWord_7973303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973303).length < 2 ^ (prefixWord ++ tailWord_7973303).sum := by decide
  have hdescent : baseEnd_7973303 < baseStart_7973303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973356 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 3]
def baseStart_7973356 : Nat := 118140960795 + 7973356 * 2 ^ 59
def prefixEnd_7973356 : Nat := 4983230072969 + 3 ^ 40 * 7973356 * 2
def baseEnd_7973356 : Nat := 4094164057410411441681209

theorem tailTrace_7973356 : CollatzResearch.WordTrace tailWord_7973356 prefixEnd_7973356 4094164057410411441681209 := by
  unfold tailWord_7973356
  simp only [CollatzResearch.WordTrace]
  refine ⟨145406092250950213818093961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193874789667933618424125281 145406092250950213818093961)
  ·
    refine ⟨109054569188212660363570471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145406092250950213818093961 109054569188212660363570471)
    ·
      refine ⟨163581853782318990545355707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109054569188212660363570471 163581853782318990545355707)
      ·
        refine ⟨245372780673478485818033561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163581853782318990545355707 245372780673478485818033561)
        ·
          refine ⟨184029585505108864363525171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245372780673478485818033561 184029585505108864363525171)
          ·
            refine ⟨276044378257663296545287757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184029585505108864363525171 276044378257663296545287757)
            ·
              refine ⟨103516641846623736204482909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276044378257663296545287757 103516641846623736204482909)
              ·
                refine ⟨38818740692483901076681091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103516641846623736204482909 38818740692483901076681091)
                ·
                  refine ⟨58228111038725851615021637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38818740692483901076681091 58228111038725851615021637)
                  ·
                    refine ⟨10917770819761097177816557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58228111038725851615021637 10917770819761097177816557)
                    ·
                      refine ⟨4094164057410411441681209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10917770819761097177816557 4094164057410411441681209)
                      ·
                        rfl

theorem cell23_7973356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_7973356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973356 prefixEnd_7973356 := by exact prefixLift 7973356
  have htrace : WordTrace (prefixWord ++ tailWord_7973356) baseStart_7973356 baseEnd_7973356 := by
    simpa [prefixWord, tailWord_7973356, baseEnd_7973356] using wordTrace_append hprefix tailTrace_7973356
  have hstable : (prefixWord ++ tailWord_7973356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973356).length < 2 ^ (prefixWord ++ tailWord_7973356).sum := by decide
  have hdescent : baseEnd_7973356 < baseStart_7973356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973373 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_7973373 : Nat := 118140960795 + 7973373 * 2 ^ 59
def prefixEnd_7973373 : Nat := 4983230072969 + 3 ^ 40 * 7973373 * 2
def baseEnd_7973373 : Nat := 4094172786581537875168631

theorem tailTrace_7973373 : CollatzResearch.WordTrace tailWord_7973373 prefixEnd_7973373 4094172786581537875168631 := by
  unfold tailWord_7973373
  simp only [CollatzResearch.WordTrace]
  refine ⟨290812804542838839539556773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193875203028559226359704515 290812804542838839539556773)
  ·
    refine ⟨54527400851782282413666895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290812804542838839539556773 54527400851782282413666895)
    ·
      refine ⟨81791101277673423620500343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54527400851782282413666895 81791101277673423620500343)
      ·
        refine ⟨122686651916510135430750515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81791101277673423620500343 122686651916510135430750515)
        ·
          refine ⟨184029977874765203146125773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122686651916510135430750515 184029977874765203146125773)
          ·
            refine ⟨69011241703036951179797165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184029977874765203146125773 69011241703036951179797165)
            ·
              refine ⟨25879215638638856692423937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69011241703036951179797165 25879215638638856692423937)
              ·
                refine ⟨19409411728979142519317953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25879215638638856692423937 19409411728979142519317953)
                ·
                  refine ⟨14557058796734356889488465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19409411728979142519317953 14557058796734356889488465)
                  ·
                    refine ⟨10917794097550767667116349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14557058796734356889488465 10917794097550767667116349)
                    ·
                      refine ⟨4094172786581537875168631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10917794097550767667116349 4094172786581537875168631)
                      ·
                        rfl

theorem cell23_7973373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_7973373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973373 prefixEnd_7973373 := by exact prefixLift 7973373
  have htrace : WordTrace (prefixWord ++ tailWord_7973373) baseStart_7973373 baseEnd_7973373 := by
    simpa [prefixWord, tailWord_7973373, baseEnd_7973373] using wordTrace_append hprefix tailTrace_7973373
  have hstable : (prefixWord ++ tailWord_7973373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973373).length < 2 ^ (prefixWord ++ tailWord_7973373).sum := by decide
  have hdescent : baseEnd_7973373 < baseStart_7973373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973380 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_7973380 : Nat := 118140960795 + 7973380 * 2 ^ 59
def prefixEnd_7973380 : Nat := 4983230072969 + 3 ^ 40 * 7973380 * 2
def baseEnd_7973380 : Nat := 1364725460315373115927033

theorem tailTrace_7973380 : CollatzResearch.WordTrace tailWord_7973380 prefixEnd_7973380 1364725460315373115927033 := by
  unfold tailWord_7973380
  simp only [CollatzResearch.WordTrace]
  refine ⟨145406529926906739867530797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193875373235875653156707729 145406529926906739867530797)
  ·
    refine ⟨54527448722590027450324049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145406529926906739867530797 54527448722590027450324049)
    ·
      refine ⟨40895586541942520587743037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54527448722590027450324049 40895586541942520587743037)
      ·
        refine ⟨15335844953228445220403639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40895586541942520587743037 15335844953228445220403639)
        ·
          refine ⟨23003767429842667830605459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15335844953228445220403639 23003767429842667830605459)
          ·
            refine ⟨34505651144764001745908189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23003767429842667830605459 34505651144764001745908189)
            ·
              refine ⟨12939619179286500654715571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34505651144764001745908189 12939619179286500654715571)
              ·
                refine ⟨19409428768929750982073357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12939619179286500654715571 19409428768929750982073357)
                ·
                  refine ⟨7278535788348656618277509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19409428768929750982073357 7278535788348656618277509)
                  ·
                    refine ⟨1364725460315373115927033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7278535788348656618277509 1364725460315373115927033)
                    ·
                      rfl

theorem cell23_7973380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_7973380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973380 prefixEnd_7973380 := by exact prefixLift 7973380
  have htrace : WordTrace (prefixWord ++ tailWord_7973380) baseStart_7973380 baseEnd_7973380 := by
    simpa [prefixWord, tailWord_7973380, baseEnd_7973380] using wordTrace_append hprefix tailTrace_7973380
  have hstable : (prefixWord ++ tailWord_7973380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973380).length < 2 ^ (prefixWord ++ tailWord_7973380).sum := by decide
  have hdescent : baseEnd_7973380 < baseStart_7973380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973413 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 1, 5, 2]
def baseStart_7973413 : Nat := 118140960795 + 7973413 * 2 ^ 59
def prefixEnd_7973413 : Nat := 4983230072969 + 3 ^ 40 * 7973413 * 2
def baseEnd_7973413 : Nat := 4094193325807717718668447

theorem tailTrace_7973413 : CollatzResearch.WordTrace tailWord_7973413 prefixEnd_7973413 4094193325807717718668447 := by
  unfold tailWord_7973413
  simp only [CollatzResearch.WordTrace]
  refine ⟨290814263462693926371012893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193876175641795950914008595 290814263462693926371012893)
  ·
    refine ⟨109055348798510222389129835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290814263462693926371012893 109055348798510222389129835)
    ·
      refine ⟨163583023197765333583694753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109055348798510222389129835 163583023197765333583694753)
      ·
        refine ⟨122687267398324000187771065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163583023197765333583694753 122687267398324000187771065)
        ·
          refine ⟨92015450548743000140828299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122687267398324000187771065 92015450548743000140828299)
          ·
            refine ⟨138023175823114500211242449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92015450548743000140828299 138023175823114500211242449)
            ·
              refine ⟨103517381867335875158431837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138023175823114500211242449 103517381867335875158431837)
              ·
                refine ⟨38819018200250953184411939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103517381867335875158431837 38819018200250953184411939)
                ·
                  refine ⟨58228527300376429776617909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38819018200250953184411939 58228527300376429776617909)
                  ·
                    refine ⟨5458924434410290291557929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58228527300376429776617909 5458924434410290291557929)
                    ·
                      refine ⟨4094193325807717718668447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458924434410290291557929 4094193325807717718668447)
                      ·
                        rfl

theorem cell23_7973413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_7973413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973413 prefixEnd_7973413 := by exact prefixLift 7973413
  have htrace : WordTrace (prefixWord ++ tailWord_7973413) baseStart_7973413 baseEnd_7973413 := by
    simpa [prefixWord, tailWord_7973413, baseEnd_7973413] using wordTrace_append hprefix tailTrace_7973413
  have hstable : (prefixWord ++ tailWord_7973413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973413).length < 2 ^ (prefixWord ++ tailWord_7973413).sum := by decide
  have hdescent : baseEnd_7973413 < baseStart_7973413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973463 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 3]
def baseStart_7973463 : Nat := 118140960795 + 7973463 * 2 ^ 59
def prefixEnd_7973463 : Nat := 4983230072969 + 3 ^ 40 * 7973463 * 2
def baseEnd_7973463 : Nat := 4094218999840442523043217

theorem tailTrace_7973463 : CollatzResearch.WordTrace tailWord_7973463 prefixEnd_7973463 4094218999840442523043217 := by
  unfold tailWord_7973463
  simp only [CollatzResearch.WordTrace]
  refine ⟨290816087112512784910333043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193877391408341856606888695 290816087112512784910333043)
  ·
    refine ⟨436224130668769177365499565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290816087112512784910333043 436224130668769177365499565)
    ·
      refine ⟨163584049000788441512062337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436224130668769177365499565 163584049000788441512062337)
      ·
        refine ⟨122688036750591331134046753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163584049000788441512062337 122688036750591331134046753)
        ·
          refine ⟨92016027562943498350535065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122688036750591331134046753 92016027562943498350535065)
          ·
            refine ⟨69012020672207623762901299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92016027562943498350535065 69012020672207623762901299)
            ·
              refine ⟨103518031008311435644351949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69012020672207623762901299 103518031008311435644351949)
              ·
                refine ⟨38819261628116788366631981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103518031008311435644351949 38819261628116788366631981)
                ·
                  refine ⟨14557223110543795637486993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38819261628116788366631981 14557223110543795637486993)
                  ·
                    refine ⟨10917917332907846728115245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14557223110543795637486993 10917917332907846728115245)
                    ·
                      refine ⟨4094218999840442523043217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10917917332907846728115245 4094218999840442523043217)
                      ·
                        rfl

theorem cell23_7973463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_7973463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973463 prefixEnd_7973463 := by exact prefixLift 7973463
  have htrace : WordTrace (prefixWord ++ tailWord_7973463) baseStart_7973463 baseEnd_7973463 := by
    simpa [prefixWord, tailWord_7973463, baseEnd_7973463] using wordTrace_append hprefix tailTrace_7973463
  have hstable : (prefixWord ++ tailWord_7973463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973463).length < 2 ^ (prefixWord ++ tailWord_7973463).sum := by decide
  have hdescent : baseEnd_7973463 < baseStart_7973463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973473 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_7973473 : Nat := 118140960795 + 7973473 * 2 ^ 59
def prefixEnd_7973473 : Nat := 4983230072969 + 3 ^ 40 * 7973473 * 2
def baseEnd_7973473 : Nat := 4094224134646987483918171

theorem tailTrace_7973473 : CollatzResearch.WordTrace tailWord_7973473 prefixEnd_7973473 4094224134646987483918171 := by
  unfold tailWord_7973473
  simp only [CollatzResearch.WordTrace]
  refine ⟨290816451842476556618197073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193877634561651037745464715 290816451842476556618197073)
  ·
    refine ⟨218112338881857417463647805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290816451842476556618197073 218112338881857417463647805)
    ·
      refine ⟨81792127080696531548867927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218112338881857417463647805 81792127080696531548867927)
      ·
        refine ⟨122688190621044797323301891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81792127080696531548867927 122688190621044797323301891)
        ·
          refine ⟨184032285931567195984952837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122688190621044797323301891 184032285931567195984952837)
          ·
            refine ⟨34506053612168849247178657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184032285931567195984952837 34506053612168849247178657)
            ·
              refine ⟨25879540209126636935383993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34506053612168849247178657 25879540209126636935383993)
              ·
                refine ⟨19409655156844977701537995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25879540209126636935383993 19409655156844977701537995)
                ·
                  refine ⟨29114482735267466552306993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19409655156844977701537995 29114482735267466552306993)
                  ·
                    refine ⟨21835862051450599914230245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29114482735267466552306993 21835862051450599914230245)
                    ·
                      refine ⟨4094224134646987483918171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21835862051450599914230245 4094224134646987483918171)
                      ·
                        rfl

theorem cell23_7973473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_7973473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973473 prefixEnd_7973473 := by exact prefixLift 7973473
  have htrace : WordTrace (prefixWord ++ tailWord_7973473) baseStart_7973473 baseEnd_7973473 := by
    simpa [prefixWord, tailWord_7973473, baseEnd_7973473] using wordTrace_append hprefix tailTrace_7973473
  have hstable : (prefixWord ++ tailWord_7973473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973473).length < 2 ^ (prefixWord ++ tailWord_7973473).sum := by decide
  have hdescent : baseEnd_7973473 < baseStart_7973473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973503 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 2, 7, 2]
def baseStart_7973503 : Nat := 118140960795 + 7973503 * 2 ^ 59
def prefixEnd_7973503 : Nat := 4983230072969 + 3 ^ 40 * 7973503 * 2
def baseEnd_7973503 : Nat := 4094239539066622366543033

theorem tailTrace_7973503 : CollatzResearch.WordTrace tailWord_7973503 prefixEnd_7973503 4094239539066622366543033 := by
  unfold tailWord_7973503
  simp only [CollatzResearch.WordTrace]
  refine ⟨290817546032367871741789163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193878364021578581161192775 290817546032367871741789163)
  ·
    refine ⟨436226319048551807612683745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290817546032367871741789163 436226319048551807612683745)
    ·
      refine ⟨327169739286413855709512809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436226319048551807612683745 327169739286413855709512809)
      ·
        refine ⟨245377304464810391782134607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327169739286413855709512809 245377304464810391782134607)
        ·
          refine ⟨368065956697215587673201911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245377304464810391782134607 368065956697215587673201911)
          ·
            refine ⟨552098935045823381509802867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368065956697215587673201911 552098935045823381509802867)
            ·
              refine ⟨828148402568735072264704301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552098935045823381509802867 828148402568735072264704301)
              ·
                refine ⟨310555650963275652099264113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 828148402568735072264704301 310555650963275652099264113)
                ·
                  refine ⟨232916738222456739074448085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310555650963275652099264113 232916738222456739074448085)
                  ·
                    refine ⟨5458986052088829822057377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 232916738222456739074448085 5458986052088829822057377)
                    ·
                      refine ⟨4094239539066622366543033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5458986052088829822057377 4094239539066622366543033)
                      ·
                        rfl

theorem cell23_7973503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 7, 2].length) (baseStart_7973503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973503 prefixEnd_7973503 := by exact prefixLift 7973503
  have htrace : WordTrace (prefixWord ++ tailWord_7973503) baseStart_7973503 baseEnd_7973503 := by
    simpa [prefixWord, tailWord_7973503, baseEnd_7973503] using wordTrace_append hprefix tailTrace_7973503
  have hstable : (prefixWord ++ tailWord_7973503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973503).length < 2 ^ (prefixWord ++ tailWord_7973503).sum := by decide
  have hdescent : baseEnd_7973503 < baseStart_7973503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973516 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_7973516 : Nat := 118140960795 + 7973516 * 2 ^ 59
def prefixEnd_7973516 : Nat := 4983230072969 + 3 ^ 40 * 7973516 * 2
def baseEnd_7973516 : Nat := 4094246214315130815680473

theorem tailTrace_7973516 : CollatzResearch.WordTrace tailWord_7973516 prefixEnd_7973516 4094246214315130815680473 := by
  unfold tailWord_7973516
  simp only [CollatzResearch.WordTrace]
  refine ⟨145409010090660387481006201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193878680120880516641341601 145409010090660387481006201)
  ·
    refine ⟨109056757567995290610754651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145409010090660387481006201 109056757567995290610754651)
    ·
      refine ⟨163585136351992935916131977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109056757567995290610754651 163585136351992935916131977)
      ·
        refine ⟨122688852263994701937098983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163585136351992935916131977 122688852263994701937098983)
        ·
          refine ⟨184033278395992052905648475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122688852263994701937098983 184033278395992052905648475)
          ·
            refine ⟨276049917593988079358472713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184033278395992052905648475 276049917593988079358472713)
            ·
              refine ⟨207037438195491059518854535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276049917593988079358472713 207037438195491059518854535)
              ·
                refine ⟨310556157293236589278281803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207037438195491059518854535 310556157293236589278281803)
                ·
                  refine ⟨465834235939854883917422705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310556157293236589278281803 465834235939854883917422705)
                  ·
                    refine ⟨349375676954891162938067029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 465834235939854883917422705 349375676954891162938067029)
                    ·
                      refine ⟨4094246214315130815680473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 349375676954891162938067029 4094246214315130815680473)
                      ·
                        rfl

theorem cell23_7973516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_7973516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973516 prefixEnd_7973516 := by exact prefixLift 7973516
  have htrace : WordTrace (prefixWord ++ tailWord_7973516) baseStart_7973516 baseEnd_7973516 := by
    simpa [prefixWord, tailWord_7973516, baseEnd_7973516] using wordTrace_append hprefix tailTrace_7973516
  have hstable : (prefixWord ++ tailWord_7973516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973516).length < 2 ^ (prefixWord ++ tailWord_7973516).sum := by decide
  have hdescent : baseEnd_7973516 < baseStart_7973516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973583 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 3]
def baseStart_7973583 : Nat := 118140960795 + 7973583 * 2 ^ 59
def prefixEnd_7973583 : Nat := 4983230072969 + 3 ^ 40 * 7973583 * 2
def baseEnd_7973583 : Nat := 4094280617518982053542665

theorem tailTrace_7973583 : CollatzResearch.WordTrace tailWord_7973583 prefixEnd_7973583 4094280617518982053542665 := by
  unfold tailWord_7973583
  simp only [CollatzResearch.WordTrace]
  refine ⟨290820463872078045404701403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193880309248052030269800935 290820463872078045404701403)
  ·
    refine ⟨436230695808117068107052105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290820463872078045404701403 436230695808117068107052105)
    ·
      refine ⟨327173021856087801080289079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436230695808117068107052105 327173021856087801080289079)
      ·
        refine ⟨490759532784131701620433619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327173021856087801080289079 490759532784131701620433619)
        ·
          refine ⟨736139299176197552430650429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490759532784131701620433619 736139299176197552430650429)
          ·
            refine ⟨276052237191074082161493911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736139299176197552430650429 276052237191074082161493911)
            ·
              refine ⟨414078355786611123242240867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276052237191074082161493911 414078355786611123242240867)
              ·
                refine ⟨621117533679916684863361301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414078355786611123242240867 621117533679916684863361301)
                ·
                  refine ⟨29114884391246094602970061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 621117533679916684863361301 29114884391246094602970061)
                  ·
                    refine ⟨10918081646717285476113773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29114884391246094602970061 10918081646717285476113773)
                    ·
                      refine ⟨4094280617518982053542665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10918081646717285476113773 4094280617518982053542665)
                      ·
                        rfl

theorem cell23_7973583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 3].length) (baseStart_7973583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973583 prefixEnd_7973583 := by exact prefixLift 7973583
  have htrace : WordTrace (prefixWord ++ tailWord_7973583) baseStart_7973583 baseEnd_7973583 := by
    simpa [prefixWord, tailWord_7973583, baseEnd_7973583] using wordTrace_append hprefix tailTrace_7973583
  have hstable : (prefixWord ++ tailWord_7973583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973583).length < 2 ^ (prefixWord ++ tailWord_7973583).sum := by decide
  have hdescent : baseEnd_7973583 < baseStart_7973583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973623 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_7973623 : Nat := 118140960795 + 7973623 * 2 ^ 59
def prefixEnd_7973623 : Nat := 4983230072969 + 3 ^ 40 * 7973623 * 2
def baseEnd_7973623 : Nat := 4094301156745161897042481

theorem tailTrace_7973623 : CollatzResearch.WordTrace tailWord_7973623 prefixEnd_7973623 4094301156745161897042481 := by
  unfold tailWord_7973623
  simp only [CollatzResearch.WordTrace]
  refine ⟨290821922791933132236157523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193881281861288754824105015 290821922791933132236157523)
  ·
    refine ⟨436232884187899698354236285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290821922791933132236157523 436232884187899698354236285)
    ·
      refine ⟨163587331570462386882838607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436232884187899698354236285 163587331570462386882838607)
      ·
        refine ⟨245380997355693580324257911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163587331570462386882838607 245380997355693580324257911)
        ·
          refine ⟨368071496033540370486386867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245380997355693580324257911 368071496033540370486386867)
          ·
            refine ⟨552107244050310555729580301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368071496033540370486386867 552107244050310555729580301)
            ·
              refine ⟨207040216518866458398592613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 552107244050310555729580301 207040216518866458398592613)
              ·
                refine ⟨38820040597287460949736115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207040216518866458398592613 38820040597287460949736115)
                ·
                  refine ⟨58230060895931191424604173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38820040597287460949736115 58230060895931191424604173)
                  ·
                    refine ⟨21836272835974196784226565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58230060895931191424604173 21836272835974196784226565)
                    ·
                      refine ⟨4094301156745161897042481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21836272835974196784226565 4094301156745161897042481)
                      ·
                        rfl

theorem cell23_7973623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_7973623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973623 prefixEnd_7973623 := by exact prefixLift 7973623
  have htrace : WordTrace (prefixWord ++ tailWord_7973623) baseStart_7973623 baseEnd_7973623 := by
    simpa [prefixWord, tailWord_7973623, baseEnd_7973623] using wordTrace_append hprefix tailTrace_7973623
  have hstable : (prefixWord ++ tailWord_7973623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973623).length < 2 ^ (prefixWord ++ tailWord_7973623).sum := by decide
  have hdescent : baseEnd_7973623 < baseStart_7973623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973640 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_7973640 : Nat := 118140960795 + 7973640 * 2 ^ 59
def prefixEnd_7973640 : Nat := 4983230072969 + 3 ^ 40 * 7973640 * 2
def baseEnd_7973640 : Nat := 4094309885916288330529903

theorem tailTrace_7973640 : CollatzResearch.WordTrace tailWord_7973640 prefixEnd_7973640 4094309885916288330529903 := by
  unfold tailWord_7973640
  simp only [CollatzResearch.WordTrace]
  refine ⟨145411271416435772069763187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193881695221914362759684249 145411271416435772069763187)
  ·
    refine ⟨218116907124653658104644781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145411271416435772069763187 218116907124653658104644781)
    ·
      refine ⟨81793840171745121789241793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218116907124653658104644781 81793840171745121789241793)
      ·
        refine ⟨61345380128808841341931345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81793840171745121789241793 61345380128808841341931345)
        ·
          refine ⟨46009035096606631006448509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61345380128808841341931345 46009035096606631006448509)
          ·
            refine ⟨17253388161227486627418191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46009035096606631006448509 17253388161227486627418191)
            ·
              refine ⟨25880082241841229941127287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17253388161227486627418191 25880082241841229941127287)
              ·
                refine ⟨38820123362761844911690931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25880082241841229941127287 38820123362761844911690931)
                ·
                  refine ⟨58230185044142767367536397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38820123362761844911690931 58230185044142767367536397)
                  ·
                    refine ⟨21836319391553537762826149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58230185044142767367536397 21836319391553537762826149)
                    ·
                      refine ⟨4094309885916288330529903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21836319391553537762826149 4094309885916288330529903)
                      ·
                        rfl

theorem cell23_7973640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_7973640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973640 prefixEnd_7973640 := by exact prefixLift 7973640
  have htrace : WordTrace (prefixWord ++ tailWord_7973640) baseStart_7973640 baseEnd_7973640 := by
    simpa [prefixWord, tailWord_7973640, baseEnd_7973640] using wordTrace_append hprefix tailTrace_7973640
  have hstable : (prefixWord ++ tailWord_7973640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973640).length < 2 ^ (prefixWord ++ tailWord_7973640).sum := by decide
  have hdescent : baseEnd_7973640 < baseStart_7973640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973653 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_7973653 : Nat := 118140960795 + 7973653 * 2 ^ 59
def prefixEnd_7973653 : Nat := 4983230072969 + 3 ^ 40 * 7973653 * 2
def baseEnd_7973653 : Nat := 4094316561164796779667343

theorem tailTrace_7973653 : CollatzResearch.WordTrace tailWord_7973653 prefixEnd_7973653 4094316561164796779667343 := by
  unfold tailWord_7973653
  simp only [CollatzResearch.WordTrace]
  refine ⟨290823016981824447359749613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193882011321216298239833075 290823016981824447359749613)
  ·
    refine ⟨109058631368184167759906105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290823016981824447359749613 109058631368184167759906105)
    ·
      refine ⟨81793973526138125819929579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109058631368184167759906105 81793973526138125819929579)
      ·
        refine ⟨122690960289207188729894369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81793973526138125819929579 122690960289207188729894369)
        ·
          refine ⟨92018220216905391547420777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122690960289207188729894369 92018220216905391547420777)
          ·
            refine ⟨69013665162679043660565583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92018220216905391547420777 69013665162679043660565583)
            ·
              refine ⟨103520497744018565490848375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69013665162679043660565583 103520497744018565490848375)
              ·
                refine ⟨155280746616027848236272563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103520497744018565490848375 155280746616027848236272563)
                ·
                  refine ⟨232921119924041772354408845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155280746616027848236272563 232921119924041772354408845)
                  ·
                    refine ⟨87345419971515664632903317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232921119924041772354408845 87345419971515664632903317)
                    ·
                      refine ⟨4094316561164796779667343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87345419971515664632903317 4094316561164796779667343)
                      ·
                        rfl

theorem cell23_7973653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_7973653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973653 prefixEnd_7973653 := by exact prefixLift 7973653
  have htrace : WordTrace (prefixWord ++ tailWord_7973653) baseStart_7973653 baseEnd_7973653 := by
    simpa [prefixWord, tailWord_7973653, baseEnd_7973653] using wordTrace_append hprefix tailTrace_7973653
  have hstable : (prefixWord ++ tailWord_7973653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973653).length < 2 ^ (prefixWord ++ tailWord_7973653).sum := by decide
  have hdescent : baseEnd_7973653 < baseStart_7973653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973740 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 1, 6]
def baseStart_7973740 : Nat := 118140960795 + 7973740 * 2 ^ 59
def prefixEnd_7973740 : Nat := 4983230072969 + 3 ^ 40 * 7973740 * 2
def baseEnd_7973740 : Nat := 1364787077993912646426481

theorem tailTrace_7973740 : CollatzResearch.WordTrace tailWord_7973740 prefixEnd_7973740 1364787077993912646426481 := by
  unfold tailWord_7973740
  simp only [CollatzResearch.WordTrace]
  refine ⟨145413095066254630609083337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193884126755006174145444449 145413095066254630609083337)
  ·
    refine ⟨109059821299690972956812503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145413095066254630609083337 109059821299690972956812503)
    ·
      refine ⟨163589731949536459435218755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109059821299690972956812503 163589731949536459435218755)
      ·
        refine ⟨245384597924304689152828133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163589731949536459435218755 245384597924304689152828133)
        ·
          refine ⟨46009612110807129216155275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245384597924304689152828133 46009612110807129216155275)
          ·
            refine ⟨69014418166210693824232913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46009612110807129216155275 69014418166210693824232913)
            ·
              refine ⟨51760813624658020368174685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69014418166210693824232913 51760813624658020368174685)
              ·
                refine ⟨19410305109246757638065507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51760813624658020368174685 19410305109246757638065507)
                ·
                  refine ⟨29115457663870136457098261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19410305109246757638065507 29115457663870136457098261)
                  ·
                    refine ⟨1364787077993912646426481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29115457663870136457098261 1364787077993912646426481)
                    ·
                      rfl

theorem cell23_7973740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_7973740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973740 prefixEnd_7973740 := by exact prefixLift 7973740
  have htrace : WordTrace (prefixWord ++ tailWord_7973740) baseStart_7973740 baseEnd_7973740 := by
    simpa [prefixWord, tailWord_7973740, baseEnd_7973740] using wordTrace_append hprefix tailTrace_7973740
  have hstable : (prefixWord ++ tailWord_7973740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973740).length < 2 ^ (prefixWord ++ tailWord_7973740).sum := by decide
  have hdescent : baseEnd_7973740 < baseStart_7973740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973747 : List Nat := [1, 1, 1, 2, 2, 1, 7, 2, 1, 1, 4]
def baseStart_7973747 : Nat := 118140960795 + 7973747 * 2 ^ 59
def prefixEnd_7973747 : Nat := 4983230072969 + 3 ^ 40 * 7973747 * 2
def baseEnd_7973747 : Nat := 4094364828346319411891911

theorem tailTrace_7973747 : CollatzResearch.WordTrace tailWord_7973747 prefixEnd_7973747 4094364828346319411891911 := by
  unfold tailWord_7973747
  simp only [CollatzResearch.WordTrace]
  refine ⟨290826445443483901413671495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193884296962322600942447663 290826445443483901413671495)
  ·
    refine ⟨436239668165225852120507243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290826445443483901413671495 436239668165225852120507243)
    ·
      refine ⟨654359502247838778180760865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436239668165225852120507243 654359502247838778180760865)
      ·
        refine ⟨490769626685879083635570649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654359502247838778180760865 490769626685879083635570649)
        ·
          refine ⟨368077220014409312726677987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490769626685879083635570649 368077220014409312726677987)
          ·
            refine ⟨552115830021613969090016981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368077220014409312726677987 552115830021613969090016981)
            ·
              refine ⟨12940214766131577400547273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 552115830021613969090016981 12940214766131577400547273)
              ·
                refine ⟨9705161074598683050410455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12940214766131577400547273 9705161074598683050410455)
                ·
                  refine ⟨14557741611898024575615683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9705161074598683050410455 14557741611898024575615683)
                  ·
                    refine ⟨21836612417847036863423525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14557741611898024575615683 21836612417847036863423525)
                    ·
                      refine ⟨4094364828346319411891911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21836612417847036863423525 4094364828346319411891911)
                      ·
                        rfl

theorem cell23_7973747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 1, 4].length) (baseStart_7973747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973747 prefixEnd_7973747 := by exact prefixLift 7973747
  have htrace : WordTrace (prefixWord ++ tailWord_7973747) baseStart_7973747 baseEnd_7973747 := by
    simpa [prefixWord, tailWord_7973747, baseEnd_7973747] using wordTrace_append hprefix tailTrace_7973747
  have hstable : (prefixWord ++ tailWord_7973747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973747).length < 2 ^ (prefixWord ++ tailWord_7973747).sum := by decide
  have hdescent : baseEnd_7973747 < baseStart_7973747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973767 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_7973767 : Nat := 118140960795 + 7973767 * 2 ^ 59
def prefixEnd_7973767 : Nat := 4983230072969 + 3 ^ 40 * 7973767 * 2
def baseEnd_7973767 : Nat := 4094375097959409333641819

theorem tailTrace_7973767 : CollatzResearch.WordTrace tailWord_7973767 prefixEnd_7973767 4094375097959409333641819 := by
  unfold tailWord_7973767
  simp only [CollatzResearch.WordTrace]
  refine ⟨290827174903411444829399555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193884783268940963219599703 290827174903411444829399555)
  ·
    refine ⟨436240762355117167244099333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290827174903411444829399555 436240762355117167244099333)
    ·
      refine ⟨81795142941584468858268625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 436240762355117167244099333 81795142941584468858268625)
      ·
        refine ⟨61346357206188351643701469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81795142941584468858268625 61346357206188351643701469)
        ·
          refine ⟨23004883952320631866388051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61346357206188351643701469 23004883952320631866388051)
          ·
            refine ⟨34507325928480947799582077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23004883952320631866388051 34507325928480947799582077)
            ·
              refine ⟨12940247223180355424843279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34507325928480947799582077 12940247223180355424843279)
              ·
                refine ⟨19410370834770533137264919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12940247223180355424843279 19410370834770533137264919)
                ·
                  refine ⟨29115556252155799705897379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19410370834770533137264919 29115556252155799705897379)
                  ·
                    refine ⟨43673334378233699558846069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29115556252155799705897379 43673334378233699558846069)
                    ·
                      refine ⟨4094375097959409333641819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43673334378233699558846069 4094375097959409333641819)
                      ·
                        rfl

theorem cell23_7973767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_7973767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973767 prefixEnd_7973767 := by exact prefixLift 7973767
  have htrace : WordTrace (prefixWord ++ tailWord_7973767) baseStart_7973767 baseEnd_7973767 := by
    simpa [prefixWord, tailWord_7973767, baseEnd_7973767] using wordTrace_append hprefix tailTrace_7973767
  have hstable : (prefixWord ++ tailWord_7973767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973767).length < 2 ^ (prefixWord ++ tailWord_7973767).sum := by decide
  have hdescent : baseEnd_7973767 < baseStart_7973767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973770 : List Nat := [3, 1, 2, 4, 1, 12]
def baseStart_7973770 : Nat := 118140960795 + 7973770 * 2 ^ 59
def prefixEnd_7973770 : Nat := 4983230072969 + 3 ^ 40 * 7973770 * 2
def baseEnd_7973770 : Nat := 16849286577783427250635

theorem tailTrace_7973770 : CollatzResearch.WordTrace tailWord_7973770 prefixEnd_7973770 16849286577783427250635 := by
  unfold tailWord_7973770
  simp only [CollatzResearch.WordTrace]
  refine ⟨72706821080600144085439691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193884856214933717561172509 72706821080600144085439691)
  ·
    refine ⟨109060231620900216128159537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72706821080600144085439691 109060231620900216128159537)
    ·
      refine ⟨81795173715675162096119653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109060231620900216128159537 81795173715675162096119653)
      ·
        refine ⟨15336595071689092893022435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81795173715675162096119653 15336595071689092893022435)
        ·
          refine ⟨23004892607533639339533653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15336595071689092893022435 23004892607533639339533653)
          ·
            refine ⟨16849286577783427250635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23004892607533639339533653 16849286577783427250635)
            ·
              rfl

theorem cell23_7973770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 12].length) (baseStart_7973770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973770 prefixEnd_7973770 := by exact prefixLift 7973770
  have htrace : WordTrace (prefixWord ++ tailWord_7973770) baseStart_7973770 baseEnd_7973770 := by
    simpa [prefixWord, tailWord_7973770, baseEnd_7973770] using wordTrace_append hprefix tailTrace_7973770
  have hstable : (prefixWord ++ tailWord_7973770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973770).length < 2 ^ (prefixWord ++ tailWord_7973770).sum := by decide
  have hdescent : baseEnd_7973770 < baseStart_7973770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973794 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_7973794 : Nat := 118140960795 + 7973794 * 2 ^ 59
def prefixEnd_7973794 : Nat := 4983230072969 + 3 ^ 40 * 7973794 * 2
def baseEnd_7973794 : Nat := 4094388961937080728004195

theorem tailTrace_7973794 : CollatzResearch.WordTrace tailWord_7973794 prefixEnd_7973794 4094388961937080728004195 := by
  unfold tailWord_7973794
  simp only [CollatzResearch.WordTrace]
  refine ⟨72707039918578407110158109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193885439782875752293754957 72707039918578407110158109)
  ·
    refine ⟨27265139969466902666309291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72707039918578407110158109 27265139969466902666309291)
    ·
      refine ⟨40897709954200353999463937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27265139969466902666309291 40897709954200353999463937)
      ·
        refine ⟨30673282465650265499597953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40897709954200353999463937 30673282465650265499597953)
        ·
          refine ⟨23004961849237699124698465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30673282465650265499597953 23004961849237699124698465)
          ·
            refine ⟨17253721386928274343523849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23004961849237699124698465 17253721386928274343523849)
            ·
              refine ⟨12940291040196205757642887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17253721386928274343523849 12940291040196205757642887)
              ·
                refine ⟨19410436560294308636464331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12940291040196205757642887 19410436560294308636464331)
                ·
                  refine ⟨29115654840441462954696497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19410436560294308636464331 29115654840441462954696497)
                  ·
                    refine ⟨21836741130331097216022373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29115654840441462954696497 21836741130331097216022373)
                    ·
                      refine ⟨4094388961937080728004195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21836741130331097216022373 4094388961937080728004195)
                      ·
                        rfl

theorem cell23_7973794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_7973794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973794 prefixEnd_7973794 := by exact prefixLift 7973794
  have htrace : WordTrace (prefixWord ++ tailWord_7973794) baseStart_7973794 baseEnd_7973794 := by
    simpa [prefixWord, tailWord_7973794, baseEnd_7973794] using wordTrace_append hprefix tailTrace_7973794
  have hstable : (prefixWord ++ tailWord_7973794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973794).length < 2 ^ (prefixWord ++ tailWord_7973794).sum := by decide
  have hdescent : baseEnd_7973794 < baseStart_7973794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973797 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 8, 1, 3]
def baseStart_7973797 : Nat := 118140960795 + 7973797 * 2 ^ 59
def prefixEnd_7973797 : Nat := 4983230072969 + 3 ^ 40 * 7973797 * 2
def baseEnd_7973797 : Nat := 4094390502379044216266681

theorem tailTrace_7973797 : CollatzResearch.WordTrace tailWord_7973797 prefixEnd_7973797 4094390502379044216266681 := by
  unfold tailWord_7973797
  simp only [CollatzResearch.WordTrace]
  refine ⟨290828269093302759952991645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193885512728868506635327763 290828269093302759952991645)
  ·
    refine ⟨109060600909988534982371867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290828269093302759952991645 109060600909988534982371867)
    ·
      refine ⟨163590901364982802473557801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109060600909988534982371867 163590901364982802473557801)
      ·
        refine ⟨122693176023737101855168351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163590901364982802473557801 122693176023737101855168351)
        ·
          refine ⟨184039764035605652782752527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122693176023737101855168351 184039764035605652782752527)
          ·
            refine ⟨276059646053408479174128791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184039764035605652782752527 276059646053408479174128791)
            ·
              refine ⟨414089469080112718761193187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276059646053408479174128791 414089469080112718761193187)
              ·
                refine ⟨621134203620169078141789781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414089469080112718761193187 621134203620169078141789781)
                ·
                  refine ⟨7278916448673856384474099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 621134203620169078141789781 7278916448673856384474099)
                  ·
                    refine ⟨10918374673010784576711149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7278916448673856384474099 10918374673010784576711149)
                    ·
                      refine ⟨4094390502379044216266681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10918374673010784576711149 4094390502379044216266681)
                      ·
                        rfl

theorem cell23_7973797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_7973797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973797 prefixEnd_7973797 := by exact prefixLift 7973797
  have htrace : WordTrace (prefixWord ++ tailWord_7973797) baseStart_7973797 baseEnd_7973797 := by
    simpa [prefixWord, tailWord_7973797, baseEnd_7973797] using wordTrace_append hprefix tailTrace_7973797
  have hstable : (prefixWord ++ tailWord_7973797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973797).length < 2 ^ (prefixWord ++ tailWord_7973797).sum := by decide
  have hdescent : baseEnd_7973797 < baseStart_7973797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973840 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 5]
def baseStart_7973840 : Nat := 118140960795 + 7973840 * 2 ^ 59
def prefixEnd_7973840 : Nat := 4983230072969 + 3 ^ 40 * 7973840 * 2
def baseEnd_7973840 : Nat := 4094412582047187548028983

theorem tailTrace_7973840 : CollatzResearch.WordTrace tailWord_7973840 prefixEnd_7973840 4094412582047187548028983 := by
  unfold tailWord_7973840
  simp only [CollatzResearch.WordTrace]
  refine ⟨145414918716073489148403487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193886558288097985531204649 145414918716073489148403487)
  ·
    refine ⟨218122378074110233722605231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145414918716073489148403487 218122378074110233722605231)
    ·
      refine ⟨327183567111165350583907847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218122378074110233722605231 327183567111165350583907847)
      ·
        refine ⟨490775350666748025875861771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327183567111165350583907847 490775350666748025875861771)
        ·
          refine ⟨736163026000122038813792657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490775350666748025875861771 736163026000122038813792657)
          ·
            refine ⟨552122269500091529110344493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736163026000122038813792657 552122269500091529110344493)
            ·
              refine ⟨207045851062534323416379185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 552122269500091529110344493 207045851062534323416379185)
              ·
                refine ⟨155284388296900742562284389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207045851062534323416379185 155284388296900742562284389)
                ·
                  refine ⟨29115822805668889230428323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155284388296900742562284389 29115822805668889230428323)
                  ·
                    refine ⟨43673734208503333845642485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29115822805668889230428323 43673734208503333845642485)
                    ·
                      refine ⟨4094412582047187548028983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43673734208503333845642485 4094412582047187548028983)
                      ·
                        rfl

theorem cell23_7973840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_7973840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973840 prefixEnd_7973840 := by exact prefixLift 7973840
  have htrace : WordTrace (prefixWord ++ tailWord_7973840) baseStart_7973840 baseEnd_7973840 := by
    simpa [prefixWord, tailWord_7973840, baseEnd_7973840] using wordTrace_append hprefix tailTrace_7973840
  have hstable : (prefixWord ++ tailWord_7973840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973840).length < 2 ^ (prefixWord ++ tailWord_7973840).sum := by decide
  have hdescent : baseEnd_7973840 < baseStart_7973840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973858 : List Nat := [3, 3, 3, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_7973858 : Nat := 118140960795 + 7973858 * 2 ^ 59
def prefixEnd_7973858 : Nat := 4983230072969 + 3 ^ 40 * 7973858 * 2
def baseEnd_7973858 : Nat := 4094421824698968477603901

theorem tailTrace_7973858 : CollatzResearch.WordTrace tailWord_7973858 prefixEnd_7973858 4094421824698968477603901 := by
  unfold tailWord_7973858
  simp only [CollatzResearch.WordTrace]
  refine ⟨72707623486520441842740557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193886995964054511580641485 72707623486520441842740557)
  ·
    refine ⟨27265358807445165691027709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72707623486520441842740557 27265358807445165691027709)
    ·
      refine ⟨10224509552791937134135391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27265358807445165691027709 10224509552791937134135391)
      ·
        refine ⟨15336764329187905701203087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10224509552791937134135391 15336764329187905701203087)
        ·
          refine ⟨23005146493781858551804631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15336764329187905701203087 23005146493781858551804631)
          ·
            refine ⟨34507719740672787827706947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23005146493781858551804631 34507719740672787827706947)
            ·
              refine ⟨51761579611009181741560421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34507719740672787827706947 51761579611009181741560421)
              ·
                refine ⟨9705296177064221576542579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51761579611009181741560421 9705296177064221576542579)
                ·
                  refine ⟨14557944265596332364813869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9705296177064221576542579 14557944265596332364813869)
                  ·
                    refine ⟨5459229099598624636805201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14557944265596332364813869 5459229099598624636805201)
                    ·
                      refine ⟨4094421824698968477603901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5459229099598624636805201 4094421824698968477603901)
                      ·
                        rfl

theorem cell23_7973858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_7973858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973858 prefixEnd_7973858 := by exact prefixLift 7973858
  have htrace : WordTrace (prefixWord ++ tailWord_7973858) baseStart_7973858 baseEnd_7973858 := by
    simpa [prefixWord, tailWord_7973858, baseEnd_7973858] using wordTrace_append hprefix tailTrace_7973858
  have hstable : (prefixWord ++ tailWord_7973858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973858).length < 2 ^ (prefixWord ++ tailWord_7973858).sum := by decide
  have hdescent : baseEnd_7973858 < baseStart_7973858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973860 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 9]
def baseStart_7973860 : Nat := 118140960795 + 7973860 * 2 ^ 59
def prefixEnd_7973860 : Nat := 4983230072969 + 3 ^ 40 * 7973860 * 2
def baseEnd_7973860 : Nat := 454935872406697496642099

theorem tailTrace_7973860 : CollatzResearch.WordTrace tailWord_7973860 prefixEnd_7973860 454935872406697496642099 := by
  unfold tailWord_7973860
  simp only [CollatzResearch.WordTrace]
  refine ⟨145415283446037260856267517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193887044594716347808356689 145415283446037260856267517)
  ·
    refine ⟨54530731292263972821100319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145415283446037260856267517 54530731292263972821100319)
    ·
      refine ⟨81796096938395959231650479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54530731292263972821100319 81796096938395959231650479)
      ·
        refine ⟨122694145407593938847475719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81796096938395959231650479 122694145407593938847475719)
        ·
          refine ⟨184041218111390908271213579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122694145407593938847475719 184041218111390908271213579)
          ·
            refine ⟨276061827167086362406820369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184041218111390908271213579 276061827167086362406820369)
            ·
              refine ⟨207046370375314771805115277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276061827167086362406820369 207046370375314771805115277)
              ·
                refine ⟨77642388890743039426918229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207046370375314771805115277 77642388890743039426918229)
                ·
                  refine ⟨454935872406697496642099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77642388890743039426918229 454935872406697496642099)
                  ·
                    rfl

theorem cell23_7973860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_7973860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973860 prefixEnd_7973860 := by exact prefixLift 7973860
  have htrace : WordTrace (prefixWord ++ tailWord_7973860) baseStart_7973860 baseEnd_7973860 := by
    simpa [prefixWord, tailWord_7973860, baseEnd_7973860] using wordTrace_append hprefix tailTrace_7973860
  have hstable : (prefixWord ++ tailWord_7973860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973860).length < 2 ^ (prefixWord ++ tailWord_7973860).sum := by decide
  have hdescent : baseEnd_7973860 < baseStart_7973860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973924 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_7973924 : Nat := 118140960795 + 7973924 * 2 ^ 59
def prefixEnd_7973924 : Nat := 4983230072969 + 3 ^ 40 * 7973924 * 2
def baseEnd_7973924 : Nat := 1364818571474055073126199

theorem tailTrace_7973924 : CollatzResearch.WordTrace tailWord_7973924 prefixEnd_7973924 1364818571474055073126199 := by
  unfold tailWord_7973924
  simp only [CollatzResearch.WordTrace]
  refine ⟨145416450581921330321432413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193888600775895107095243217 145416450581921330321432413)
  ·
    refine ⟨54531168968220498870537155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145416450581921330321432413 54531168968220498870537155)
    ·
      refine ⟨81796753452330748305805733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54531168968220498870537155 81796753452330748305805733)
      ·
        refine ⟨15336891272312015307338575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81796753452330748305805733 15336891272312015307338575)
        ·
          refine ⟨23005336908468022961007863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15336891272312015307338575 23005336908468022961007863)
          ·
            refine ⟨34508005362702034441511795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23005336908468022961007863 34508005362702034441511795)
            ·
              refine ⟨51762008044053051662267693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34508005362702034441511795 51762008044053051662267693)
              ·
                refine ⟨19410753016519894373350385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51762008044053051662267693 19410753016519894373350385)
                ·
                  refine ⟨14558064762389920780012789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19410753016519894373350385 14558064762389920780012789)
                  ·
                    refine ⟨1364818571474055073126199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14558064762389920780012789 1364818571474055073126199)
                    ·
                      rfl

theorem cell23_7973924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_7973924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973924 prefixEnd_7973924 := by exact prefixLift 7973924
  have htrace : WordTrace (prefixWord ++ tailWord_7973924) baseStart_7973924 baseEnd_7973924 := by
    simpa [prefixWord, tailWord_7973924, baseEnd_7973924] using wordTrace_append hprefix tailTrace_7973924
  have hstable : (prefixWord ++ tailWord_7973924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973924).length < 2 ^ (prefixWord ++ tailWord_7973924).sum := by decide
  have hdescent : baseEnd_7973924 < baseStart_7973924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973944 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_7973944 : Nat := 118140960795 + 7973944 * 2 ^ 59
def prefixEnd_7973944 : Nat := 4983230072969 + 3 ^ 40 * 7973944 * 2
def baseEnd_7973944 : Nat := 4094465984035255141128505

theorem tailTrace_7973944 : CollatzResearch.WordTrace tailWord_7973944 prefixEnd_7973944 4094465984035255141128505 := by
  unfold tailWord_7973944
  simp only [CollatzResearch.WordTrace]
  refine ⟨145416815311885102029296443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193889087082513469372395257 145416815311885102029296443)
  ·
    refine ⟨218125222967827653043944665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145416815311885102029296443 218125222967827653043944665)
    ·
      refine ⟨163593917225870739782958499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218125222967827653043944665 163593917225870739782958499)
      ·
        refine ⟨245390875838806109674437749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163593917225870739782958499 245390875838806109674437749)
        ·
          refine ⟨23005394609888072781978539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245390875838806109674437749 23005394609888072781978539)
          ·
            refine ⟨34508091914832109172967809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23005394609888072781978539 34508091914832109172967809)
            ·
              refine ⟨25881068936124081879725857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34508091914832109172967809 25881068936124081879725857)
              ·
                refine ⟨19410801702093061409794393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25881068936124081879725857 19410801702093061409794393)
                ·
                  refine ⟨14558101276569796057345795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19410801702093061409794393 14558101276569796057345795)
                  ·
                    refine ⟨21837151914854694086018693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14558101276569796057345795 21837151914854694086018693)
                    ·
                      refine ⟨4094465984035255141128505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21837151914854694086018693 4094465984035255141128505)
                      ·
                        rfl

theorem cell23_7973944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_7973944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973944 prefixEnd_7973944 := by exact prefixLift 7973944
  have htrace : WordTrace (prefixWord ++ tailWord_7973944) baseStart_7973944 baseEnd_7973944 := by
    simpa [prefixWord, tailWord_7973944, baseEnd_7973944] using wordTrace_append hprefix tailTrace_7973944
  have hstable : (prefixWord ++ tailWord_7973944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973944).length < 2 ^ (prefixWord ++ tailWord_7973944).sum := by decide
  have hdescent : baseEnd_7973944 < baseStart_7973944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7973977 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 1, 7, 3]
def baseStart_7973977 : Nat := 118140960795 + 7973977 * 2 ^ 59
def prefixEnd_7973977 : Nat := 4983230072969 + 3 ^ 40 * 7973977 * 2
def baseEnd_7973977 : Nat := 4094482928896853512015853

theorem tailTrace_7973977 : CollatzResearch.WordTrace tailWord_7973977 prefixEnd_7973977 4094482928896853512015853 := by
  unfold tailWord_7973977
  simp only [CollatzResearch.WordTrace]
  refine ⟨290834834232650650694544185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193889889488433767129696123 290834834232650650694544185)
  ·
    refine ⟨218126125674487988020908139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290834834232650650694544185 218126125674487988020908139)
    ·
      refine ⟨327189188511731982031362209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218126125674487988020908139 327189188511731982031362209)
      ·
        refine ⟨245391891383798986523521657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327189188511731982031362209 245391891383798986523521657)
        ·
          refine ⟨184043918537849239892641243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245391891383798986523521657 184043918537849239892641243)
          ·
            refine ⟨276065877806773859838961865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184043918537849239892641243 276065877806773859838961865)
            ·
              refine ⟨207049408355080394879221399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276065877806773859838961865 207049408355080394879221399)
              ·
                refine ⟨310574112532620592318832099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207049408355080394879221399 310574112532620592318832099)
                ·
                  refine ⟨465861168798930888478248149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310574112532620592318832099 465861168798930888478248149)
                  ·
                    refine ⟨10918621143724942698708941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 465861168798930888478248149 10918621143724942698708941)
                    ·
                      refine ⟨4094482928896853512015853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10918621143724942698708941 4094482928896853512015853)
                      ·
                        rfl

theorem cell23_7973977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_7973977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7973977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7973977 prefixEnd_7973977 := by exact prefixLift 7973977
  have htrace : WordTrace (prefixWord ++ tailWord_7973977) baseStart_7973977 baseEnd_7973977 := by
    simpa [prefixWord, tailWord_7973977, baseEnd_7973977] using wordTrace_append hprefix tailTrace_7973977
  have hstable : (prefixWord ++ tailWord_7973977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7973977).length < 2 ^ (prefixWord ++ tailWord_7973977).sum := by decide
  have hdescent : baseEnd_7973977 < baseStart_7973977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7973977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974051 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 5, 2, 2]
def baseStart_7974051 : Nat := 118140960795 + 7974051 * 2 ^ 59
def prefixEnd_7974051 : Nat := 4983230072969 + 3 ^ 40 * 7974051 * 2
def baseEnd_7974051 : Nat := 4094520926465286222490513

theorem tailTrace_7974051 : CollatzResearch.WordTrace tailWord_7974051 prefixEnd_7974051 4094520926465286222490513 := by
  unfold tailWord_7974051
  simp only [CollatzResearch.WordTrace]
  refine ⟨290837533234382561332738007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193891688822921707555158671 290837533234382561332738007)
  ·
    refine ⟨436256299851573841999107011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290837533234382561332738007 436256299851573841999107011)
    ·
      refine ⟨654384449777360762998660517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436256299851573841999107011 654384449777360762998660517)
      ·
        refine ⟨122697084333255143062248847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 654384449777360762998660517 122697084333255143062248847)
        ·
          refine ⟨184045626499882714593373271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122697084333255143062248847 184045626499882714593373271)
          ·
            refine ⟨276068439749824071890059907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184045626499882714593373271 276068439749824071890059907)
            ·
              refine ⟨414102659624736107835089861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276068439749824071890059907 414102659624736107835089861)
              ·
                refine ⟨77644248679638020219079349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 414102659624736107835089861 77644248679638020219079349)
                ·
                  refine ⟨7279148313716064395538689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77644248679638020219079349 7279148313716064395538689)
                  ·
                    refine ⟨5459361235287048296654017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7279148313716064395538689 5459361235287048296654017)
                    ·
                      refine ⟨4094520926465286222490513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5459361235287048296654017 4094520926465286222490513)
                      ·
                        rfl

theorem cell23_7974051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_7974051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974051 prefixEnd_7974051 := by exact prefixLift 7974051
  have htrace : WordTrace (prefixWord ++ tailWord_7974051) baseStart_7974051 baseEnd_7974051 := by
    simpa [prefixWord, tailWord_7974051, baseEnd_7974051] using wordTrace_append hprefix tailTrace_7974051
  have hstable : (prefixWord ++ tailWord_7974051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974051).length < 2 ^ (prefixWord ++ tailWord_7974051).sum := by decide
  have hdescent : baseEnd_7974051 < baseStart_7974051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974078 : List Nat := [4, 2, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_7974078 : Nat := 118140960795 + 7974078 * 2 ^ 59
def prefixEnd_7974078 : Nat := 4983230072969 + 3 ^ 40 * 7974078 * 2
def baseEnd_7974078 : Nat := 1364844930147652538950963

theorem tailTrace_7974078 : CollatzResearch.WordTrace tailWord_7974078 prefixEnd_7974078 1364844930147652538950963 := by
  unfold tailWord_7974078
  simp only [CollatzResearch.WordTrace]
  refine ⟨36354814750660593117996361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193892345336856496629313925 36354814750660593117996361)
  ·
    refine ⟨27266111062995444838497271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36354814750660593117996361 27266111062995444838497271)
    ·
      refine ⟨40899166594493167257745907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27266111062995444838497271 40899166594493167257745907)
      ·
        refine ⟨61348749891739750886618861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40899166594493167257745907 61348749891739750886618861)
        ·
          refine ⟨23005781209402406582482073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61348749891739750886618861 23005781209402406582482073)
          ·
            refine ⟨17254335907051804936861555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23005781209402406582482073 17254335907051804936861555)
            ·
              refine ⟨25881503860577707405292333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17254335907051804936861555 25881503860577707405292333)
              ·
                refine ⟨9705563947716640276984625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25881503860577707405292333 9705563947716640276984625)
                ·
                  refine ⟨7279172960787480207738469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9705563947716640276984625 7279172960787480207738469)
                  ·
                    refine ⟨1364844930147652538950963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7279172960787480207738469 1364844930147652538950963)
                    ·
                      rfl

theorem cell23_7974078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_7974078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974078 prefixEnd_7974078 := by exact prefixLift 7974078
  have htrace : WordTrace (prefixWord ++ tailWord_7974078) baseStart_7974078 baseEnd_7974078 := by
    simpa [prefixWord, tailWord_7974078, baseEnd_7974078] using wordTrace_append hprefix tailTrace_7974078
  have hstable : (prefixWord ++ tailWord_7974078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974078).length < 2 ^ (prefixWord ++ tailWord_7974078).sum := by decide
  have hdescent : baseEnd_7974078 < baseStart_7974078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974081 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_7974081 : Nat := 118140960795 + 7974081 * 2 ^ 59
def prefixEnd_7974081 : Nat := 4983230072969 + 3 ^ 40 * 7974081 * 2
def baseEnd_7974081 : Nat := 4094536330884921105115375

theorem tailTrace_7974081 : CollatzResearch.WordTrace tailWord_7974081 prefixEnd_7974081 4094536330884921105115375 := by
  unfold tailWord_7974081
  simp only [CollatzResearch.WordTrace]
  refine ⟨290838627424273876456330097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193892418282849250970886731 290838627424273876456330097)
  ·
    refine ⟨218128970568205407342247573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290838627424273876456330097 218128970568205407342247573)
    ·
      refine ⟨10224795495384628469167855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 218128970568205407342247573 10224795495384628469167855)
      ·
        refine ⟨15337193243076942703751783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10224795495384628469167855 15337193243076942703751783)
        ·
          refine ⟨23005789864615414055627675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15337193243076942703751783 23005789864615414055627675)
          ·
            refine ⟨34508684796923121083441513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23005789864615414055627675 34508684796923121083441513)
            ·
              refine ⟨25881513597692340812581135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34508684796923121083441513 25881513597692340812581135)
              ·
                refine ⟨38822270396538511218871703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25881513597692340812581135 38822270396538511218871703)
                ·
                  refine ⟨58233405594807766828307555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38822270396538511218871703 58233405594807766828307555)
                  ·
                    refine ⟨87350108392211650242461333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58233405594807766828307555 87350108392211650242461333)
                    ·
                      refine ⟨4094536330884921105115375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87350108392211650242461333 4094536330884921105115375)
                      ·
                        rfl

theorem cell23_7974081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_7974081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974081 prefixEnd_7974081 := by exact prefixLift 7974081
  have htrace : WordTrace (prefixWord ++ tailWord_7974081) baseStart_7974081 baseEnd_7974081 := by
    simpa [prefixWord, tailWord_7974081, baseEnd_7974081] using wordTrace_append hprefix tailTrace_7974081
  have hstable : (prefixWord ++ tailWord_7974081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974081).length < 2 ^ (prefixWord ++ tailWord_7974081).sum := by decide
  have hdescent : baseEnd_7974081 < baseStart_7974081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974082 : List Nat := [3, 5, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_7974082 : Nat := 118140960795 + 7974082 * 2 ^ 59
def prefixEnd_7974082 : Nat := 4983230072969 + 3 ^ 40 * 7974082 * 2
def baseEnd_7974082 : Nat := 1364845614788525200400957

theorem tailTrace_7974082 : CollatzResearch.WordTrace tailWord_7974082 prefixEnd_7974082 1364845614788525200400957 := by
  unfold tailWord_7974082
  simp only [CollatzResearch.WordTrace]
  refine ⟨72709665974317563406779125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193892442598180169084744333 72709665974317563406779125)
  ·
    refine ⟨6816531185092271569385543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72709665974317563406779125 6816531185092271569385543)
    ·
      refine ⟨10224796777638407354078315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6816531185092271569385543 10224796777638407354078315)
      ·
        refine ⟨15337195166457611031117473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10224796777638407354078315 15337195166457611031117473)
        ·
          refine ⟨11502896374843208273338105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15337195166457611031117473 11502896374843208273338105)
          ·
            refine ⟨8627172281132406205003579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11502896374843208273338105 8627172281132406205003579)
            ·
              refine ⟨12940758421698609307505369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8627172281132406205003579 12940758421698609307505369)
              ·
                refine ⟨9705568816273956980629027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12940758421698609307505369 9705568816273956980629027)
                ·
                  refine ⟨14558353224410935470943541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9705568816273956980629027 14558353224410935470943541)
                  ·
                    refine ⟨1364845614788525200400957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14558353224410935470943541 1364845614788525200400957)
                    ·
                      rfl

theorem cell23_7974082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_7974082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974082 prefixEnd_7974082 := by exact prefixLift 7974082
  have htrace : WordTrace (prefixWord ++ tailWord_7974082) baseStart_7974082 baseEnd_7974082 := by
    simpa [prefixWord, tailWord_7974082, baseEnd_7974082] using wordTrace_append hprefix tailTrace_7974082
  have hstable : (prefixWord ++ tailWord_7974082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974082).length < 2 ^ (prefixWord ++ tailWord_7974082).sum := by decide
  have hdescent : baseEnd_7974082 < baseStart_7974082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974101 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_7974101 : Nat := 118140960795 + 7974101 * 2 ^ 59
def prefixEnd_7974101 : Nat := 4983230072969 + 3 ^ 40 * 7974101 * 2
def baseEnd_7974101 : Nat := 4094546600498011026865283

theorem tailTrace_7974101 : CollatzResearch.WordTrace tailWord_7974101 prefixEnd_7974101 4094546600498011026865283 := by
  unfold tailWord_7974101
  simp only [CollatzResearch.WordTrace]
  refine ⟨290839356884201419872058157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193892904589467613248038771 290839356884201419872058157)
  ·
    refine ⟨109064758831575532452021809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290839356884201419872058157 109064758831575532452021809)
    ·
      refine ⟨81798569123681649339016357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109064758831575532452021809 81798569123681649339016357)
      ·
        refine ⟨15337231710690309251065567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81798569123681649339016357 15337231710690309251065567)
        ·
          refine ⟨23005847566035463876598351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15337231710690309251065567 23005847566035463876598351)
          ·
            refine ⟨34508771349053195814897527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23005847566035463876598351 34508771349053195814897527)
            ·
              refine ⟨51763157023579793722346291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34508771349053195814897527 51763157023579793722346291)
              ·
                refine ⟨77644735535369690583519437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51763157023579793722346291 77644735535369690583519437)
                ·
                  refine ⟨29116775825763633968819789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77644735535369690583519437 29116775825763633968819789)
                  ·
                    refine ⟨10918790934661362738307421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29116775825763633968819789 10918790934661362738307421)
                    ·
                      refine ⟨4094546600498011026865283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10918790934661362738307421 4094546600498011026865283)
                      ·
                        rfl

theorem cell23_7974101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_7974101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974101 prefixEnd_7974101 := by exact prefixLift 7974101
  have htrace : WordTrace (prefixWord ++ tailWord_7974101) baseStart_7974101 baseEnd_7974101 := by
    simpa [prefixWord, tailWord_7974101, baseEnd_7974101] using wordTrace_append hprefix tailTrace_7974101
  have hstable : (prefixWord ++ tailWord_7974101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974101).length < 2 ^ (prefixWord ++ tailWord_7974101).sum := by decide
  have hdescent : baseEnd_7974101 < baseStart_7974101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974102 : List Nat := [5, 2, 1, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_7974102 : Nat := 118140960795 + 7974102 * 2 ^ 59
def prefixEnd_7974102 : Nat := 4983230072969 + 3 ^ 40 * 7974102 * 2
def baseEnd_7974102 : Nat := 4094547113978665522952779

theorem tailTrace_7974102 : CollatzResearch.WordTrace tailWord_7974102 prefixEnd_7974102 4094547113978665522952779 := by
  unfold tailWord_7974102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18177462084824862315177785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193892928904798531361896373 18177462084824862315177785)
  ·
    refine ⟨13633096563618646736383339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18177462084824862315177785 13633096563618646736383339)
    ·
      refine ⟨20449644845427970104575009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13633096563618646736383339 20449644845427970104575009)
      ·
        refine ⟨15337233634070977578431257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20449644845427970104575009 15337233634070977578431257)
        ·
          refine ⟨11502925225553233183823443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15337233634070977578431257 11502925225553233183823443)
          ·
            refine ⟨17254387838329849775735165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11502925225553233183823443 17254387838329849775735165)
            ·
              refine ⟨6470395439373693665900687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17254387838329849775735165 6470395439373693665900687)
              ·
                refine ⟨9705593159060540498851031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6470395439373693665900687 9705593159060540498851031)
                ·
                  refine ⟨14558389738590810748276547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9705593159060540498851031 14558389738590810748276547)
                  ·
                    refine ⟨21837584607886216122414821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14558389738590810748276547 21837584607886216122414821)
                    ·
                      refine ⟨4094547113978665522952779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21837584607886216122414821 4094547113978665522952779)
                      ·
                        rfl

theorem cell23_7974102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_7974102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974102 prefixEnd_7974102 := by exact prefixLift 7974102
  have htrace : WordTrace (prefixWord ++ tailWord_7974102) baseStart_7974102 baseEnd_7974102 := by
    simpa [prefixWord, tailWord_7974102, baseEnd_7974102] using wordTrace_append hprefix tailTrace_7974102
  have hstable : (prefixWord ++ tailWord_7974102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974102).length < 2 ^ (prefixWord ++ tailWord_7974102).sum := by decide
  have hdescent : baseEnd_7974102 < baseStart_7974102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974124 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_7974124 : Nat := 118140960795 + 7974124 * 2 ^ 59
def prefixEnd_7974124 : Nat := 4983230072969 + 3 ^ 40 * 7974124 * 2
def baseEnd_7974124 : Nat := 4094558410553064436877677

theorem tailTrace_7974124 : CollatzResearch.WordTrace tailWord_7974124 prefixEnd_7974124 4094558410553064436877677 := by
  unfold tailWord_7974124
  simp only [CollatzResearch.WordTrace]
  refine ⟨145420097881559047400072713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193893463842078729866763617 145420097881559047400072713)
  ·
    refine ⟨109065073411169285550054535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145420097881559047400072713 109065073411169285550054535)
    ·
      refine ⟨163597610116753928325081803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109065073411169285550054535 163597610116753928325081803)
      ·
        refine ⟨245396415175130892487622705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163597610116753928325081803 245396415175130892487622705)
        ·
          refine ⟨184047311381348169365717029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245396415175130892487622705 184047311381348169365717029)
          ·
            refine ⟨34508870884002781756071943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184047311381348169365717029 34508870884002781756071943)
            ·
              refine ⟨51763306326004172634107915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34508870884002781756071943 51763306326004172634107915)
              ·
                refine ⟨77644959489006258951161873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51763306326004172634107915 77644959489006258951161873)
                ·
                  refine ⟨58233719616754694213371405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77644959489006258951161873 58233719616754694213371405)
                  ·
                    refine ⟨21837644856283010330014277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58233719616754694213371405 21837644856283010330014277)
                    ·
                      refine ⟨4094558410553064436877677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21837644856283010330014277 4094558410553064436877677)
                      ·
                        rfl

theorem cell23_7974124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_7974124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974124 prefixEnd_7974124 := by exact prefixLift 7974124
  have htrace : WordTrace (prefixWord ++ tailWord_7974124) baseStart_7974124 baseEnd_7974124 := by
    simpa [prefixWord, tailWord_7974124, baseEnd_7974124] using wordTrace_append hprefix tailTrace_7974124
  have hstable : (prefixWord ++ tailWord_7974124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974124).length < 2 ^ (prefixWord ++ tailWord_7974124).sum := by decide
  have hdescent : baseEnd_7974124 < baseStart_7974124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974132 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7974132 : Nat := 118140960795 + 7974132 * 2 ^ 59
def prefixEnd_7974132 : Nat := 4983230072969 + 3 ^ 40 * 7974132 * 2
def baseEnd_7974132 : Nat := 4094562518398300405577641

theorem tailTrace_7974132 : CollatzResearch.WordTrace tailWord_7974132 prefixEnd_7974132 4094562518398300405577641 := by
  unfold tailWord_7974132
  simp only [CollatzResearch.WordTrace]
  refine ⟨145420243773544556083218325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193893658364726074777624433 145420243773544556083218325)
  ·
    refine ⟨6816573926884901066400859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145420243773544556083218325 6816573926884901066400859)
    ·
      refine ⟨10224860890327351599601289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6816573926884901066400859 10224860890327351599601289)
      ·
        refine ⟨7668645667745513699700967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10224860890327351599601289 7668645667745513699700967)
        ·
          refine ⟨11502968501618270549551451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7668645667745513699700967 11502968501618270549551451)
          ·
            refine ⟨17254452752427405824327177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11502968501618270549551451 17254452752427405824327177)
            ·
              refine ⟨12940839564320554368245383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17254452752427405824327177 12940839564320554368245383)
              ·
                refine ⟨19411259346480831552368075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12940839564320554368245383 19411259346480831552368075)
                ·
                  refine ⟨29116889019721247328552113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19411259346480831552368075 29116889019721247328552113)
                  ·
                    refine ⟨21837666764790935496414085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29116889019721247328552113 21837666764790935496414085)
                    ·
                      refine ⟨4094562518398300405577641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21837666764790935496414085 4094562518398300405577641)
                      ·
                        rfl

theorem cell23_7974132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7974132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974132 prefixEnd_7974132 := by exact prefixLift 7974132
  have htrace : WordTrace (prefixWord ++ tailWord_7974132) baseStart_7974132 baseEnd_7974132 := by
    simpa [prefixWord, tailWord_7974132, baseEnd_7974132] using wordTrace_append hprefix tailTrace_7974132
  have hstable : (prefixWord ++ tailWord_7974132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974132).length < 2 ^ (prefixWord ++ tailWord_7974132).sum := by decide
  have hdescent : baseEnd_7974132 < baseStart_7974132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974144 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 3]
def baseStart_7974144 : Nat := 118140960795 + 7974144 * 2 ^ 59
def prefixEnd_7974144 : Nat := 4983230072969 + 3 ^ 40 * 7974144 * 2
def baseEnd_7974144 : Nat := 4094568680166154358627585

theorem tailTrace_7974144 : CollatzResearch.WordTrace tailWord_7974144 prefixEnd_7974144 4094568680166154358627585 := by
  unfold tailWord_7974144
  simp only [CollatzResearch.WordTrace]
  refine ⟨145420462611522819107936743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193893950148697092143915657 145420462611522819107936743)
  ·
    refine ⟨218130693917284228661905115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145420462611522819107936743 218130693917284228661905115)
    ·
      refine ⟨327196040875926342992857673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218130693917284228661905115 327196040875926342992857673)
      ·
        refine ⟨245397030656944757244643255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327196040875926342992857673 245397030656944757244643255)
        ·
          refine ⟨368095545985417135866964883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245397030656944757244643255 368095545985417135866964883)
          ·
            refine ⟨552143318978125703800447325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368095545985417135866964883 552143318978125703800447325)
            ·
              refine ⟨207053744616797138925167747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 552143318978125703800447325 207053744616797138925167747)
              ·
                refine ⟨310580616925195708387751621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207053744616797138925167747 310580616925195708387751621)
                ·
                  refine ⟨58233865673474195322703429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310580616925195708387751621 58233865673474195322703429)
                  ·
                    refine ⟨10918849813776411623006893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58233865673474195322703429 10918849813776411623006893)
                    ·
                      refine ⟨4094568680166154358627585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10918849813776411623006893 4094568680166154358627585)
                      ·
                        rfl

theorem cell23_7974144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_7974144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974144 prefixEnd_7974144 := by exact prefixLift 7974144
  have htrace : WordTrace (prefixWord ++ tailWord_7974144) baseStart_7974144 baseEnd_7974144 := by
    simpa [prefixWord, tailWord_7974144, baseEnd_7974144] using wordTrace_append hprefix tailTrace_7974144
  have hstable : (prefixWord ++ tailWord_7974144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974144).length < 2 ^ (prefixWord ++ tailWord_7974144).sum := by decide
  have hdescent : baseEnd_7974144 < baseStart_7974144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974154 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_7974154 : Nat := 118140960795 + 7974154 * 2 ^ 59
def prefixEnd_7974154 : Nat := 4983230072969 + 3 ^ 40 * 7974154 * 2
def baseEnd_7974154 : Nat := 4094573814972699319502539

theorem tailTrace_7974154 : CollatzResearch.WordTrace tailWord_7974154 prefixEnd_7974154 4094573814972699319502539 := by
  unfold tailWord_7974154
  simp only [CollatzResearch.WordTrace]
  refine ⟨72710322488252352480934379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193894193302006273282491677 72710322488252352480934379)
  ·
    refine ⟨109065483732378528721401569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72710322488252352480934379 109065483732378528721401569)
    ·
      refine ⟨81799112799283896541051177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109065483732378528721401569 81799112799283896541051177)
      ·
        refine ⟨61349334599462922405788383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81799112799283896541051177 61349334599462922405788383)
        ·
          refine ⟨92024001899194383608682575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61349334599462922405788383 92024001899194383608682575)
          ·
            refine ⟨138036002848791575413023863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92024001899194383608682575 138036002848791575413023863)
            ·
              refine ⟨207054004273187363119535795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138036002848791575413023863 207054004273187363119535795)
              ·
                refine ⟨310581006409781044679303693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207054004273187363119535795 310581006409781044679303693)
                ·
                  refine ⟨116467877403667891754738885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310581006409781044679303693 116467877403667891754738885)
                  ·
                    refine ⟨21837727013187729704013541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116467877403667891754738885 21837727013187729704013541)
                    ·
                      refine ⟨4094573814972699319502539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21837727013187729704013541 4094573814972699319502539)
                      ·
                        rfl

theorem cell23_7974154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_7974154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974154 prefixEnd_7974154 := by exact prefixLift 7974154
  have htrace : WordTrace (prefixWord ++ tailWord_7974154) baseStart_7974154 baseEnd_7974154 := by
    simpa [prefixWord, tailWord_7974154, baseEnd_7974154] using wordTrace_append hprefix tailTrace_7974154
  have hstable : (prefixWord ++ tailWord_7974154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974154).length < 2 ^ (prefixWord ++ tailWord_7974154).sum := by decide
  have hdescent : baseEnd_7974154 < baseStart_7974154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974158 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2]
def baseStart_7974158 : Nat := 118140960795 + 7974158 * 2 ^ 59
def prefixEnd_7974158 : Nat := 4983230072969 + 3 ^ 40 * 7974158 * 2
def baseEnd_7974158 : Nat := 4094575868895317303852521

theorem tailTrace_7974158 : CollatzResearch.WordTrace tailWord_7974158 prefixEnd_7974158 4094575868895317303852521 := by
  unfold tailWord_7974158
  simp only [CollatzResearch.WordTrace]
  refine ⟨36355179480624364825860391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193894290563329945737922085 36355179480624364825860391)
  ·
    refine ⟨54532769220936547238790587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36355179480624364825860391 54532769220936547238790587)
    ·
      refine ⟨81799153831404820858185881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54532769220936547238790587 81799153831404820858185881)
      ·
        refine ⟨61349365373553615643639411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81799153831404820858185881 61349365373553615643639411)
        ·
          refine ⟨92024048060330423465459117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61349365373553615643639411 92024048060330423465459117)
          ·
            refine ⟨34509018022623908799547169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92024048060330423465459117 34509018022623908799547169)
            ·
              refine ⟨25881763516967931599660377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34509018022623908799547169 25881763516967931599660377)
              ·
                refine ⟨19411322637725948699745283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25881763516967931599660377 19411322637725948699745283)
                ·
                  refine ⟨29116983956588923049617925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19411322637725948699745283 29116983956588923049617925)
                  ·
                    refine ⟨5459434491860423071803361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29116983956588923049617925 5459434491860423071803361)
                    ·
                      refine ⟨4094575868895317303852521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5459434491860423071803361 4094575868895317303852521)
                      ·
                        rfl

theorem cell23_7974158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_7974158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974158 prefixEnd_7974158 := by exact prefixLift 7974158
  have htrace : WordTrace (prefixWord ++ tailWord_7974158) baseStart_7974158 baseEnd_7974158 := by
    simpa [prefixWord, tailWord_7974158, baseEnd_7974158] using wordTrace_append hprefix tailTrace_7974158
  have hstable : (prefixWord ++ tailWord_7974158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974158).length < 2 ^ (prefixWord ++ tailWord_7974158).sum := by decide
  have hdescent : baseEnd_7974158 < baseStart_7974158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974175 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 4, 2, 2]
def baseStart_7974175 : Nat := 118140960795 + 7974175 * 2 ^ 59
def prefixEnd_7974175 : Nat := 4983230072969 + 3 ^ 40 * 7974175 * 2
def baseEnd_7974175 : Nat := 4094584598066443737339943

theorem tailTrace_7974175 : CollatzResearch.WordTrace tailWord_7974175 prefixEnd_7974175 4094584598066443737339943 := by
  unfold tailWord_7974175
  simp only [CollatzResearch.WordTrace]
  refine ⟨290842055885933330510251979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193894703923955553673501319 290842055885933330510251979)
  ·
    refine ⟨436263083828899995765377969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290842055885933330510251979 436263083828899995765377969)
    ·
      refine ⟨327197312871674996824033477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436263083828899995765377969 327197312871674996824033477)
      ·
        refine ⟨61349496163439061904506277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327197312871674996824033477 61349496163439061904506277)
        ·
          refine ⟨11503030530644824107094927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61349496163439061904506277 11503030530644824107094927)
          ·
            refine ⟨17254545795967236160642391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11503030530644824107094927 17254545795967236160642391)
            ·
              refine ⟨25881818693950854240963587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17254545795967236160642391 25881818693950854240963587)
              ·
                refine ⟨38822728040926281361445381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25881818693950854240963587 38822728040926281361445381)
                ·
                  refine ⟨7279261507673677755271009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38822728040926281361445381 7279261507673677755271009)
                  ·
                    refine ⟨5459446130755258316453257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7279261507673677755271009 5459446130755258316453257)
                    ·
                      refine ⟨4094584598066443737339943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5459446130755258316453257 4094584598066443737339943)
                      ·
                        rfl

theorem cell23_7974175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_7974175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974175 prefixEnd_7974175 := by exact prefixLift 7974175
  have htrace : WordTrace (prefixWord ++ tailWord_7974175) baseStart_7974175 baseEnd_7974175 := by
    simpa [prefixWord, tailWord_7974175, baseEnd_7974175] using wordTrace_append hprefix tailTrace_7974175
  have hstable : (prefixWord ++ tailWord_7974175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974175).length < 2 ^ (prefixWord ++ tailWord_7974175).sum := by decide
  have hdescent : baseEnd_7974175 < baseStart_7974175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974181 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 7]
def baseStart_7974181 : Nat := 118140960795 + 7974181 * 2 ^ 59
def prefixEnd_7974181 : Nat := 4983230072969 + 3 ^ 40 * 7974181 * 2
def baseEnd_7974181 : Nat := 454954186550041190429435

theorem tailTrace_7974181 : CollatzResearch.WordTrace tailWord_7974181 prefixEnd_7974181 454954186550041190429435 := by
  unfold tailWord_7974181
  simp only [CollatzResearch.WordTrace]
  refine ⟨290842274723911593534970397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193894849815941062356646931 290842274723911593534970397)
  ·
    refine ⟨109065853021466847575613899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290842274723911593534970397 109065853021466847575613899)
    ·
      refine ⟨163598779532200271363420849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109065853021466847575613899 163598779532200271363420849)
      ·
        refine ⟨122699084649150203522565637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163598779532200271363420849 122699084649150203522565637)
        ·
          refine ⟨23006078371715663160481057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122699084649150203522565637 23006078371715663160481057)
          ·
            refine ⟨17254558778786747370360793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23006078371715663160481057 17254558778786747370360793)
            ·
              refine ⟨12940919084090060527770595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17254558778786747370360793 12940919084090060527770595)
              ·
                refine ⟨19411378626135090791655893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12940919084090060527770595 19411378626135090791655893)
                ·
                  refine ⟨454954186550041190429435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19411378626135090791655893 454954186550041190429435)
                  ·
                    rfl

theorem cell23_7974181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_7974181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974181 prefixEnd_7974181 := by exact prefixLift 7974181
  have htrace : WordTrace (prefixWord ++ tailWord_7974181) baseStart_7974181 baseEnd_7974181 := by
    simpa [prefixWord, tailWord_7974181, baseEnd_7974181] using wordTrace_append hprefix tailTrace_7974181
  have hstable : (prefixWord ++ tailWord_7974181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974181).length < 2 ^ (prefixWord ++ tailWord_7974181).sum := by decide
  have hdescent : baseEnd_7974181 < baseStart_7974181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974231 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_7974231 : Nat := 118140960795 + 7974231 * 2 ^ 59
def prefixEnd_7974231 : Nat := 4983230072969 + 3 ^ 40 * 7974231 * 2
def baseEnd_7974231 : Nat := 4094613352983095518239685

theorem tailTrace_7974231 : CollatzResearch.WordTrace tailWord_7974231 prefixEnd_7974231 4094613352983095518239685 := by
  unfold tailWord_7974231
  simp only [CollatzResearch.WordTrace]
  refine ⟨290844098373730452074290547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193896065582486968049527031 290844098373730452074290547)
  ·
    refine ⟨436266147560595678111435821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290844098373730452074290547 436266147560595678111435821)
    ·
      refine ⟨163599805335223379291788433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436266147560595678111435821 163599805335223379291788433)
      ·
        refine ⟨122699854001417534468841325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163599805335223379291788433 122699854001417534468841325)
        ·
          refine ⟨46012445250531575425815497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122699854001417534468841325 46012445250531575425815497)
          ·
            refine ⟨34509333937898681569361623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46012445250531575425815497 34509333937898681569361623)
            ·
              refine ⟨51764000906848022354042435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34509333937898681569361623 51764000906848022354042435)
              ·
                refine ⟨77646001360272033531063653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51764000906848022354042435 77646001360272033531063653)
                ·
                  refine ⟨14558625255051006287074435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77646001360272033531063653 14558625255051006287074435)
                  ·
                    refine ⟨21837937882576509430611653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14558625255051006287074435 21837937882576509430611653)
                    ·
                      refine ⟨4094613352983095518239685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21837937882576509430611653 4094613352983095518239685)
                      ·
                        rfl

theorem cell23_7974231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_7974231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974231 prefixEnd_7974231 := by exact prefixLift 7974231
  have htrace : WordTrace (prefixWord ++ tailWord_7974231) baseStart_7974231 baseEnd_7974231 := by
    simpa [prefixWord, tailWord_7974231, baseEnd_7974231] using wordTrace_append hprefix tailTrace_7974231
  have hstable : (prefixWord ++ tailWord_7974231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974231).length < 2 ^ (prefixWord ++ tailWord_7974231).sum := by decide
  have hdescent : baseEnd_7974231 < baseStart_7974231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974268 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_7974268 : Nat := 118140960795 + 7974268 * 2 ^ 59
def prefixEnd_7974268 : Nat := 4983230072969 + 3 ^ 40 * 7974268 * 2
def baseEnd_7974268 : Nat := 4094632351767311873477015

theorem tailTrace_7974268 : CollatzResearch.WordTrace tailWord_7974268 prefixEnd_7974268 4094632351767311873477015 := by
  unfold tailWord_7974268
  simp only [CollatzResearch.WordTrace]
  refine ⟨145422723937298203696693729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193896965249730938262258305 145422723937298203696693729)
  ·
    refine ⟨109067042952973652772520297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145422723937298203696693729 109067042952973652772520297)
    ·
      refine ⟨81800282214730239579390223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109067042952973652772520297 81800282214730239579390223)
      ·
        refine ⟨122700423322095359369085335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81800282214730239579390223 122700423322095359369085335)
        ·
          refine ⟨184050634983143039053628003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122700423322095359369085335 184050634983143039053628003)
          ·
            refine ⟨276075952474714558580442005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184050634983143039053628003 276075952474714558580442005)
            ·
              refine ⟨12941060272252244933458219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 276075952474714558580442005 12941060272252244933458219)
              ·
                refine ⟨19411590408378367400187329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12941060272252244933458219 19411590408378367400187329)
                ·
                  refine ⟨14558692806283775550140497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19411590408378367400187329 14558692806283775550140497)
                  ·
                    refine ⟨10919019604712831662605373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14558692806283775550140497 10919019604712831662605373)
                    ·
                      refine ⟨4094632351767311873477015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10919019604712831662605373 4094632351767311873477015)
                      ·
                        rfl

theorem cell23_7974268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_7974268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974268 prefixEnd_7974268 := by exact prefixLift 7974268
  have htrace : WordTrace (prefixWord ++ tailWord_7974268) baseStart_7974268 baseEnd_7974268 := by
    simpa [prefixWord, tailWord_7974268, baseEnd_7974268] using wordTrace_append hprefix tailTrace_7974268
  have hstable : (prefixWord ++ tailWord_7974268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974268).length < 2 ^ (prefixWord ++ tailWord_7974268).sum := by decide
  have hdescent : baseEnd_7974268 < baseStart_7974268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974292 : List Nat := [2, 4, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_7974292 : Nat := 118140960795 + 7974292 * 2 ^ 59
def prefixEnd_7974292 : Nat := 4983230072969 + 3 ^ 40 * 7974292 * 2
def baseEnd_7974292 : Nat := 1364881558434339926525635

theorem tailTrace_7974292 : CollatzResearch.WordTrace tailWord_7974292 prefixEnd_7974292 1364881558434339926525635 := by
  unfold tailWord_7974292
  simp only [CollatzResearch.WordTrace]
  refine ⟨145423161613254729746130565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193897548817672972994840753 145423161613254729746130565)
  ·
    refine ⟨27266842802485261827399481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145423161613254729746130565 27266842802485261827399481)
    ·
      refine ⟨20450132101863946370549611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27266842802485261827399481 20450132101863946370549611)
      ·
        refine ⟨30675198152795919555824417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20450132101863946370549611 30675198152795919555824417)
        ·
          refine ⟨23006398614596939666868313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30675198152795919555824417 23006398614596939666868313)
          ·
            refine ⟨17254798960947704750151235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23006398614596939666868313 17254798960947704750151235)
            ·
              refine ⟨25882198441421557125226853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17254798960947704750151235 25882198441421557125226853)
              ·
                refine ⟨4852912207766541960980035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25882198441421557125226853 4852912207766541960980035)
                ·
                  refine ⟨7279368311649812941470053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852912207766541960980035 7279368311649812941470053)
                  ·
                    refine ⟨1364881558434339926525635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7279368311649812941470053 1364881558434339926525635)
                    ·
                      rfl

theorem cell23_7974292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_7974292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974292 prefixEnd_7974292 := by exact prefixLift 7974292
  have htrace : WordTrace (prefixWord ++ tailWord_7974292) baseStart_7974292 baseEnd_7974292 := by
    simpa [prefixWord, tailWord_7974292, baseEnd_7974292] using wordTrace_append hprefix tailTrace_7974292
  have hstable : (prefixWord ++ tailWord_7974292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974292).length < 2 ^ (prefixWord ++ tailWord_7974292).sum := by decide
  have hdescent : baseEnd_7974292 < baseStart_7974292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974308 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 1, 5, 2]
def baseStart_7974308 : Nat := 118140960795 + 7974308 * 2 ^ 59
def prefixEnd_7974308 : Nat := 4983230072969 + 3 ^ 40 * 7974308 * 2
def baseEnd_7974308 : Nat := 4094652890993491716976831

theorem tailTrace_7974308 : CollatzResearch.WordTrace tailWord_7974308 prefixEnd_7974308 4094652890993491716976831 := by
  unfold tailWord_7974308
  simp only [CollatzResearch.WordTrace]
  refine ⟨145423453397225747112421789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193897937862967662816562385 145423453397225747112421789)
  ·
    refine ⟨54533795023959655167158171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145423453397225747112421789 54533795023959655167158171)
    ·
      refine ⟨81800692535939482750737257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54533795023959655167158171 81800692535939482750737257)
      ·
        refine ⟨61350519401954612063052943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81800692535939482750737257 61350519401954612063052943)
        ·
          refine ⟨92025779102931918094579415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61350519401954612063052943 92025779102931918094579415)
          ·
            refine ⟨138038668654397877141869123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92025779102931918094579415 138038668654397877141869123)
            ·
              refine ⟨207058002981596815712803685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138038668654397877141869123 207058002981596815712803685)
              ·
                refine ⟨38823375559049402946150691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207058002981596815712803685 38823375559049402946150691)
                ·
                  refine ⟨58235063338574104419226037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38823375559049402946150691 58235063338574104419226037)
                  ·
                    refine ⟨5459537187991322289302441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58235063338574104419226037 5459537187991322289302441)
                    ·
                      refine ⟨4094652890993491716976831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5459537187991322289302441 4094652890993491716976831)
                      ·
                        rfl

theorem cell23_7974308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_7974308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974308 prefixEnd_7974308 := by exact prefixLift 7974308
  have htrace : WordTrace (prefixWord ++ tailWord_7974308) baseStart_7974308 baseEnd_7974308 := by
    simpa [prefixWord, tailWord_7974308, baseEnd_7974308] using wordTrace_append hprefix tailTrace_7974308
  have hstable : (prefixWord ++ tailWord_7974308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974308).length < 2 ^ (prefixWord ++ tailWord_7974308).sum := by decide
  have hdescent : baseEnd_7974308 < baseStart_7974308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974311 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_7974311 : Nat := 118140960795 + 7974311 * 2 ^ 59
def prefixEnd_7974311 : Nat := 4983230072969 + 3 ^ 40 * 7974311 * 2
def baseEnd_7974311 : Nat := 4094654431435455205239317

theorem tailTrace_7974311 : CollatzResearch.WordTrace tailWord_7974311 prefixEnd_7974311 4094654431435455205239317 := by
  unfold tailWord_7974311
  simp only [CollatzResearch.WordTrace]
  refine ⟨290847016213440625737202787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193898010808960417158135191 290847016213440625737202787)
  ·
    refine ⟨436270524320160938605804181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290847016213440625737202787 436270524320160938605804181)
    ·
      refine ⟨20450180827507543997147071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 436270524320160938605804181 20450180827507543997147071)
      ·
        refine ⟨30675271241261315995720607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20450180827507543997147071 30675271241261315995720607)
        ·
          refine ⟨46012906861891973993580911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30675271241261315995720607 46012906861891973993580911)
          ·
            refine ⟨69019360292837960990371367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46012906861891973993580911 69019360292837960990371367)
            ·
              refine ⟨103529040439256941485557051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69019360292837960990371367 103529040439256941485557051)
              ·
                refine ⟨155293560658885412228335577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103529040439256941485557051 155293560658885412228335577)
                ·
                  refine ⟨116470170494164059171251683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155293560658885412228335577 116470170494164059171251683)
                  ·
                    refine ⟨174705255741246088756877525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116470170494164059171251683 174705255741246088756877525)
                    ·
                      refine ⟨4094654431435455205239317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174705255741246088756877525 4094654431435455205239317)
                      ·
                        rfl

theorem cell23_7974311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_7974311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974311 prefixEnd_7974311 := by exact prefixLift 7974311
  have htrace : WordTrace (prefixWord ++ tailWord_7974311) baseStart_7974311 baseEnd_7974311 := by
    simpa [prefixWord, tailWord_7974311, baseEnd_7974311] using wordTrace_append hprefix tailTrace_7974311
  have hstable : (prefixWord ++ tailWord_7974311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974311).length < 2 ^ (prefixWord ++ tailWord_7974311).sum := by decide
  have hdescent : baseEnd_7974311 < baseStart_7974311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974325 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_7974325 : Nat := 118140960795 + 7974325 * 2 ^ 59
def prefixEnd_7974325 : Nat := 4983230072969 + 3 ^ 40 * 7974325 * 2
def baseEnd_7974325 : Nat := 4094661620164618150464253

theorem tailTrace_7974325 : CollatzResearch.WordTrace tailWord_7974325 prefixEnd_7974325 4094661620164618150464253 := by
  unfold tailWord_7974325
  simp only [CollatzResearch.WordTrace]
  refine ⟨290847526835389906128212429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193898351223593270752141619 290847526835389906128212429)
  ·
    refine ⟨109067822563271214798079661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290847526835389906128212429 109067822563271214798079661)
    ·
      refine ⟨40900433461226705549279873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109067822563271214798079661 40900433461226705549279873)
      ·
        refine ⟨30675325095920029161959905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40900433461226705549279873 30675325095920029161959905)
        ·
          refine ⟨23006493821940021871469929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30675325095920029161959905 23006493821940021871469929)
          ·
            refine ⟨17254870366455016403602447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23006493821940021871469929 17254870366455016403602447)
            ·
              refine ⟨25882305549682524605403671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17254870366455016403602447 25882305549682524605403671)
              ·
                refine ⟨38823458324523786908105507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25882305549682524605403671 38823458324523786908105507)
                ·
                  refine ⟨58235187486785680362158261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38823458324523786908105507 58235187486785680362158261)
                  ·
                    refine ⟨5459548826886157533952337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58235187486785680362158261 5459548826886157533952337)
                    ·
                      refine ⟨4094661620164618150464253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5459548826886157533952337 4094661620164618150464253)
                      ·
                        rfl

theorem cell23_7974325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_7974325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974325 prefixEnd_7974325 := by exact prefixLift 7974325
  have htrace : WordTrace (prefixWord ++ tailWord_7974325) baseStart_7974325 baseEnd_7974325 := by
    simpa [prefixWord, tailWord_7974325, baseEnd_7974325] using wordTrace_append hprefix tailTrace_7974325
  have hstable : (prefixWord ++ tailWord_7974325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974325).length < 2 ^ (prefixWord ++ tailWord_7974325).sum := by decide
  have hdescent : baseEnd_7974325 < baseStart_7974325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974351 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 4]
def baseStart_7974351 : Nat := 118140960795 + 7974351 * 2 ^ 59
def prefixEnd_7974351 : Nat := 4983230072969 + 3 ^ 40 * 7974351 * 2
def baseEnd_7974351 : Nat := 4094674970661635048739133

theorem tailTrace_7974351 : CollatzResearch.WordTrace tailWord_7974351 prefixEnd_7974351 4094674970661635048739133 := by
  unfold tailWord_7974351
  simp only [CollatzResearch.WordTrace]
  refine ⟨290848475133295712568658907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193898983422197141712439271 290848475133295712568658907)
  ·
    refine ⟨436272712699943568852988361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290848475133295712568658907 436272712699943568852988361)
    ·
      refine ⟨327204534524957676639741271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436272712699943568852988361 327204534524957676639741271)
      ·
        refine ⟨490806801787436514959611907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327204534524957676639741271 490806801787436514959611907)
        ·
          refine ⟨736210202681154772439417861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490806801787436514959611907 736210202681154772439417861)
          ·
            refine ⟨138039413002716519832390849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 736210202681154772439417861 138039413002716519832390849)
            ·
              refine ⟨103529559752037389874293137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138039413002716519832390849 103529559752037389874293137)
              ·
                refine ⟨77647169814028042405719853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103529559752037389874293137 77647169814028042405719853)
                ·
                  refine ⟨29117688680260515902144945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77647169814028042405719853 29117688680260515902144945)
                  ·
                    refine ⟨21838266510195386926608709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29117688680260515902144945 21838266510195386926608709)
                    ·
                      refine ⟨4094674970661635048739133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21838266510195386926608709 4094674970661635048739133)
                      ·
                        rfl

theorem cell23_7974351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_7974351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974351 prefixEnd_7974351 := by exact prefixLift 7974351
  have htrace : WordTrace (prefixWord ++ tailWord_7974351) baseStart_7974351 baseEnd_7974351 := by
    simpa [prefixWord, tailWord_7974351, baseEnd_7974351] using wordTrace_append hprefix tailTrace_7974351
  have hstable : (prefixWord ++ tailWord_7974351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974351).length < 2 ^ (prefixWord ++ tailWord_7974351).sum := by decide
  have hdescent : baseEnd_7974351 < baseStart_7974351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974365 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_7974365 : Nat := 118140960795 + 7974365 * 2 ^ 59
def prefixEnd_7974365 : Nat := 4983230072969 + 3 ^ 40 * 7974365 * 2
def baseEnd_7974365 : Nat := 1364894053130265997988023

theorem tailTrace_7974365 : CollatzResearch.WordTrace tailWord_7974365 prefixEnd_7974365 1364894053130265997988023 := by
  unfold tailWord_7974365
  simp only [CollatzResearch.WordTrace]
  refine ⟨290848985755244992959668549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193899323836829995306445699 290848985755244992959668549)
  ·
    refine ⟨54534184829108436179937853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290848985755244992959668549 54534184829108436179937853)
    ·
      refine ⟨20450319310915663567476695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54534184829108436179937853 20450319310915663567476695)
      ·
        refine ⟨30675478966373495351215043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20450319310915663567476695 30675478966373495351215043)
        ·
          refine ⟨46013218449560243026822565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30675478966373495351215043 46013218449560243026822565)
          ·
            refine ⟨8627478459292545567529231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46013218449560243026822565 8627478459292545567529231)
            ·
              refine ⟨12941217688938818351293847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8627478459292545567529231 12941217688938818351293847)
              ·
                refine ⟨19411826533408227526940771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12941217688938818351293847 19411826533408227526940771)
                ·
                  refine ⟨29117739800112341290411157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19411826533408227526940771 29117739800112341290411157)
                  ·
                    refine ⟨1364894053130265997988023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29117739800112341290411157 1364894053130265997988023)
                    ·
                      rfl

theorem cell23_7974365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_7974365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974365 prefixEnd_7974365 := by exact prefixLift 7974365
  have htrace : WordTrace (prefixWord ++ tailWord_7974365) baseStart_7974365 baseEnd_7974365 := by
    simpa [prefixWord, tailWord_7974365, baseEnd_7974365] using wordTrace_append hprefix tailTrace_7974365
  have hstable : (prefixWord ++ tailWord_7974365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974365).length < 2 ^ (prefixWord ++ tailWord_7974365).sum := by decide
  have hdescent : baseEnd_7974365 < baseStart_7974365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974375 : List Nat := [1, 1, 5, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_7974375 : Nat := 118140960795 + 7974375 * 2 ^ 59
def prefixEnd_7974375 : Nat := 4983230072969 + 3 ^ 40 * 7974375 * 2
def baseEnd_7974375 : Nat := 4094687294197342954839023

theorem tailTrace_7974375 : CollatzResearch.WordTrace tailWord_7974375 prefixEnd_7974375 4094687294197342954839023 := by
  unfold tailWord_7974375
  simp only [CollatzResearch.WordTrace]
  refine ⟨290849350485208764667532579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193899566990139176445021719 290849350485208764667532579)
  ·
    refine ⟨436274025727813147001298869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290849350485208764667532579 436274025727813147001298869)
    ·
      refine ⟨40900689911982482531371769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 436274025727813147001298869 40900689911982482531371769)
      ·
        refine ⟨30675517433986861898528827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40900689911982482531371769 30675517433986861898528827)
        ·
          refine ⟨46013276150980292847793241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30675517433986861898528827 46013276150980292847793241)
          ·
            refine ⟨34509957113235219635844931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46013276150980292847793241 34509957113235219635844931)
            ·
              refine ⟨51764935669852829453767397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34509957113235219635844931 51764935669852829453767397)
              ·
                refine ⟨9705925438097405522581387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51764935669852829453767397 9705925438097405522581387)
                ·
                  refine ⟨14558888157146108283872081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9705925438097405522581387 14558888157146108283872081)
                  ·
                    refine ⟨10919166117859581212904061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14558888157146108283872081 10919166117859581212904061)
                    ·
                      refine ⟨4094687294197342954839023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10919166117859581212904061 4094687294197342954839023)
                      ·
                        rfl

theorem cell23_7974375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_7974375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974375 prefixEnd_7974375 := by exact prefixLift 7974375
  have htrace : WordTrace (prefixWord ++ tailWord_7974375) baseStart_7974375 baseEnd_7974375 := by
    simpa [prefixWord, tailWord_7974375, baseEnd_7974375] using wordTrace_append hprefix tailTrace_7974375
  have hstable : (prefixWord ++ tailWord_7974375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974375).length < 2 ^ (prefixWord ++ tailWord_7974375).sum := by decide
  have hdescent : baseEnd_7974375 < baseStart_7974375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974378 : List Nat := [3, 1, 3, 1, 4, 1, 1, 9]
def baseStart_7974378 : Nat := 118140960795 + 7974378 * 2 ^ 59
def prefixEnd_7974378 : Nat := 4983230072969 + 3 ^ 40 * 7974378 * 2
def baseEnd_7974378 : Nat := 151655142023678016411167

theorem tailTrace_7974378 : CollatzResearch.WordTrace tailWord_7974378 prefixEnd_7974378 151655142023678016411167 := by
  unfold tailWord_7974378
  simp only [CollatzResearch.WordTrace]
  refine ⟨72712364976049474044972947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193899639936131930786594525 72712364976049474044972947)
  ·
    refine ⟨109068547464074211067459421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72712364976049474044972947 109068547464074211067459421)
    ·
      refine ⟨40900705299027829150297283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109068547464074211067459421 40900705299027829150297283)
      ·
        refine ⟨61351057948541743725445925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40900705299027829150297283 61351057948541743725445925)
        ·
          refine ⟨11503323365351576948521111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61351057948541743725445925 11503323365351576948521111)
          ·
            refine ⟨17254985048027365422781667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11503323365351576948521111 17254985048027365422781667)
            ·
              refine ⟨25882477572041048134172501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17254985048027365422781667 25882477572041048134172501)
              ·
                refine ⟨151655142023678016411167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25882477572041048134172501 151655142023678016411167)
                ·
                  rfl

theorem cell23_7974378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 9].length) (baseStart_7974378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974378 prefixEnd_7974378 := by exact prefixLift 7974378
  have htrace : WordTrace (prefixWord ++ tailWord_7974378) baseStart_7974378 baseEnd_7974378 := by
    simpa [prefixWord, tailWord_7974378, baseEnd_7974378] using wordTrace_append hprefix tailTrace_7974378
  have hstable : (prefixWord ++ tailWord_7974378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974378).length < 2 ^ (prefixWord ++ tailWord_7974378).sum := by decide
  have hdescent : baseEnd_7974378 < baseStart_7974378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974405 : List Nat := [1, 3, 1, 1, 2, 2, 1, 6, 2, 1, 3]
def baseStart_7974405 : Nat := 118140960795 + 7974405 * 2 ^ 59
def prefixEnd_7974405 : Nat := 4983230072969 + 3 ^ 40 * 7974405 * 2
def baseEnd_7974405 : Nat := 4094702698616977837463885

theorem tailTrace_7974405 : CollatzResearch.WordTrace tailWord_7974405 prefixEnd_7974405 4094702698616977837463885 := by
  unfold tailWord_7974405
  simp only [CollatzResearch.WordTrace]
  refine ⟨290850444675100079791124669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193900296450066719860749779 290850444675100079791124669)
  ·
    refine ⟨109068916753162529921671751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290850444675100079791124669 109068916753162529921671751)
    ·
      refine ⟨163603375129743794882507627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109068916753162529921671751 163603375129743794882507627)
      ·
        refine ⟨245405062694615692323761441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163603375129743794882507627 245405062694615692323761441)
        ·
          refine ⟨184053797020961769242821081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245405062694615692323761441 184053797020961769242821081)
          ·
            refine ⟨138040347765721326932115811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184053797020961769242821081 138040347765721326932115811)
            ·
              refine ⟨207060521648581990398173717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138040347765721326932115811 207060521648581990398173717)
              ·
                refine ⟨9705961952277280799914393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207060521648581990398173717 9705961952277280799914393)
                ·
                  refine ⟨7279471464207960599935795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9705961952277280799914393 7279471464207960599935795)
                  ·
                    refine ⟨10919207196311940899903693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7279471464207960599935795 10919207196311940899903693)
                    ·
                      refine ⟨4094702698616977837463885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10919207196311940899903693 4094702698616977837463885)
                      ·
                        rfl

theorem cell23_7974405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_7974405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974405 prefixEnd_7974405 := by exact prefixLift 7974405
  have htrace : WordTrace (prefixWord ++ tailWord_7974405) baseStart_7974405 baseEnd_7974405 := by
    simpa [prefixWord, tailWord_7974405, baseEnd_7974405] using wordTrace_append hprefix tailTrace_7974405
  have hstable : (prefixWord ++ tailWord_7974405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974405).length < 2 ^ (prefixWord ++ tailWord_7974405).sum := by decide
  have hdescent : baseEnd_7974405 < baseStart_7974405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974432 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 3, 3, 2]
def baseStart_7974432 : Nat := 118140960795 + 7974432 * 2 ^ 59
def prefixEnd_7974432 : Nat := 4983230072969 + 3 ^ 40 * 7974432 * 2
def baseEnd_7974432 : Nat := 4094716562594649231826261

theorem tailTrace_7974432 : CollatzResearch.WordTrace tailWord_7974432 prefixEnd_7974432 4094716562594649231826261 := by
  unfold tailWord_7974432
  simp only [CollatzResearch.WordTrace]
  refine ⟨145425714723001131701178775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193900952964001508934905033 145425714723001131701178775)
  ·
    refine ⟨218138572084501697551768163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145425714723001131701178775 218138572084501697551768163)
    ·
      refine ⟨327207858126752546327652245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218138572084501697551768163 327207858126752546327652245)
      ·
        refine ⟨15337868349691525609108699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 327207858126752546327652245 15337868349691525609108699)
        ·
          refine ⟨23006802524537288413663049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15337868349691525609108699 23006802524537288413663049)
          ·
            refine ⟨17255101893402966310247287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23006802524537288413663049 17255101893402966310247287)
            ·
              refine ⟨25882652840104449465370931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17255101893402966310247287 25882652840104449465370931)
              ·
                refine ⟨38823979260156674198056397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25882652840104449465370931 38823979260156674198056397)
                ·
                  refine ⟨14558992222558752824271149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38823979260156674198056397 14558992222558752824271149)
                  ·
                    refine ⟨5459622083459532309101681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14558992222558752824271149 5459622083459532309101681)
                    ·
                      refine ⟨4094716562594649231826261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5459622083459532309101681 4094716562594649231826261)
                      ·
                        rfl

theorem cell23_7974432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_7974432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974432 prefixEnd_7974432 := by exact prefixLift 7974432
  have htrace : WordTrace (prefixWord ++ tailWord_7974432) baseStart_7974432 baseEnd_7974432 := by
    simpa [prefixWord, tailWord_7974432, baseEnd_7974432] using wordTrace_append hprefix tailTrace_7974432
  have hstable : (prefixWord ++ tailWord_7974432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974432).length < 2 ^ (prefixWord ++ tailWord_7974432).sum := by decide
  have hdescent : baseEnd_7974432 < baseStart_7974432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974458 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_7974458 : Nat := 118140960795 + 7974458 * 2 ^ 59
def prefixEnd_7974458 : Nat := 4983230072969 + 3 ^ 40 * 7974458 * 2
def baseEnd_7974458 : Nat := 4094729913091666130101141

theorem tailTrace_7974458 : CollatzResearch.WordTrace tailWord_7974458 prefixEnd_7974458 4094729913091666130101141 := by
  unfold tailWord_7974458
  simp only [CollatzResearch.WordTrace]
  refine ⟨72713094435977017460701007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193901585162605379895202685 72713094435977017460701007)
  ·
    refine ⟨109069641653965526191051511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72713094435977017460701007 109069641653965526191051511)
    ·
      refine ⟨163604462480948289286577267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109069641653965526191051511 163604462480948289286577267)
      ·
        refine ⟨245406693721422433929865901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163604462480948289286577267 245406693721422433929865901)
        ·
          refine ⟨92027510145533412723699713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245406693721422433929865901 92027510145533412723699713)
          ·
            refine ⟨69020632609150059542774785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92027510145533412723699713 69020632609150059542774785)
            ·
              refine ⟨51765474456862544657081089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69020632609150059542774785 51765474456862544657081089)
              ·
                refine ⟨38824105842646908492810817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51765474456862544657081089 38824105842646908492810817)
                ·
                  refine ⟨29118079381985181369608113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38824105842646908492810817 29118079381985181369608113)
                  ·
                    refine ⟨21838559536488886027206085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29118079381985181369608113 21838559536488886027206085)
                    ·
                      refine ⟨4094729913091666130101141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21838559536488886027206085 4094729913091666130101141)
                      ·
                        rfl

theorem cell23_7974458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_7974458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974458 prefixEnd_7974458 := by exact prefixLift 7974458
  have htrace : WordTrace (prefixWord ++ tailWord_7974458) baseStart_7974458 baseEnd_7974458 := by
    simpa [prefixWord, tailWord_7974458, baseEnd_7974458] using wordTrace_append hprefix tailTrace_7974458
  have hstable : (prefixWord ++ tailWord_7974458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974458).length < 2 ^ (prefixWord ++ tailWord_7974458).sum := by decide
  have hdescent : baseEnd_7974458 < baseStart_7974458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974578 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_7974578 : Nat := 118140960795 + 7974578 * 2 ^ 59
def prefixEnd_7974578 : Nat := 4983230072969 + 3 ^ 40 * 7974578 * 2
def baseEnd_7974578 : Nat := 4094791530770205660600589

theorem tailTrace_7974578 : CollatzResearch.WordTrace tailWord_7974578 prefixEnd_7974578 4094791530770205660600589 := by
  unfold tailWord_7974578
  simp only [CollatzResearch.WordTrace]
  refine ⟨72714188625868332584293097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193904503002315553558114925 72714188625868332584293097)
  ·
    refine ⟨54535641469401249438219823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72714188625868332584293097 54535641469401249438219823)
    ·
      refine ⟨81803462204101874157329735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54535641469401249438219823 81803462204101874157329735)
      ·
        refine ⟨122705193306152811235994603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81803462204101874157329735 122705193306152811235994603)
        ·
          refine ⟨184057789959229216853991905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122705193306152811235994603 184057789959229216853991905)
          ·
            refine ⟨138043342469421912640493929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184057789959229216853991905 138043342469421912640493929)
            ·
              refine ⟨103532506852066434480370447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138043342469421912640493929 103532506852066434480370447)
              ·
                refine ⟨155298760278099651720555671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103532506852066434480370447 155298760278099651720555671)
                ·
                  refine ⟨232948140417149477580833507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155298760278099651720555671 232948140417149477580833507)
                  ·
                    refine ⟨349422210625724216371250261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 232948140417149477580833507 349422210625724216371250261)
                    ·
                      refine ⟨4094791530770205660600589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 349422210625724216371250261 4094791530770205660600589)
                      ·
                        rfl

theorem cell23_7974578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_7974578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974578 prefixEnd_7974578 := by exact prefixLift 7974578
  have htrace : WordTrace (prefixWord ++ tailWord_7974578) baseStart_7974578 baseEnd_7974578 := by
    simpa [prefixWord, tailWord_7974578, baseEnd_7974578] using wordTrace_append hprefix tailTrace_7974578
  have hstable : (prefixWord ++ tailWord_7974578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974578).length < 2 ^ (prefixWord ++ tailWord_7974578).sum := by decide
  have hdescent : baseEnd_7974578 < baseStart_7974578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974579 : List Nat := [1, 1, 1, 2, 3, 3, 5, 2, 1, 4]
def baseStart_7974579 : Nat := 118140960795 + 7974579 * 2 ^ 59
def prefixEnd_7974579 : Nat := 4983230072969 + 3 ^ 40 * 7974579 * 2
def baseEnd_7974579 : Nat := 1364930681416953385562695

theorem tailTrace_7974579 : CollatzResearch.WordTrace tailWord_7974579 prefixEnd_7974579 1364930681416953385562695 := by
  unfold tailWord_7974579
  simp only [CollatzResearch.WordTrace]
  refine ⟨290856790976469707507958791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193904527317646471671972527 290856790976469707507958791)
  ·
    refine ⟨436285186464704561261938187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290856790976469707507958791 436285186464704561261938187)
    ·
      refine ⟨654427779697056841892907281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436285186464704561261938187 654427779697056841892907281)
      ·
        refine ⟨490820834772792631419680461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654427779697056841892907281 490820834772792631419680461)
        ·
          refine ⟨184057813039797236782380173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490820834772792631419680461 184057813039797236782380173)
          ·
            refine ⟨69021679889923963793392565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184057813039797236782380173 69021679889923963793392565)
            ·
              refine ⟨6470782489680371605630553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69021679889923963793392565 6470782489680371605630553)
              ·
                refine ⟨4853086867260278704222915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6470782489680371605630553 4853086867260278704222915)
                ·
                  refine ⟨7279630300890418056334373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4853086867260278704222915 7279630300890418056334373)
                  ·
                    refine ⟨1364930681416953385562695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7279630300890418056334373 1364930681416953385562695)
                    ·
                      rfl

theorem cell23_7974579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 1, 4].length) (baseStart_7974579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974579 prefixEnd_7974579 := by exact prefixLift 7974579
  have htrace : WordTrace (prefixWord ++ tailWord_7974579) baseStart_7974579 baseEnd_7974579 := by
    simpa [prefixWord, tailWord_7974579, baseEnd_7974579] using wordTrace_append hprefix tailTrace_7974579
  have hstable : (prefixWord ++ tailWord_7974579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974579).length < 2 ^ (prefixWord ++ tailWord_7974579).sum := by decide
  have hdescent : baseEnd_7974579 < baseStart_7974579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974635 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 4, 4]
def baseStart_7974635 : Nat := 118140960795 + 7974635 * 2 ^ 59
def prefixEnd_7974635 : Nat := 4983230072969 + 3 ^ 40 * 7974635 * 2
def baseEnd_7974635 : Nat := 1364940266389170645862609

theorem tailTrace_7974635 : CollatzResearch.WordTrace tailWord_7974635 prefixEnd_7974635 1364940266389170645862609 := by
  unfold tailWord_7974635
  simp only [CollatzResearch.WordTrace]
  refine ⟨290858833464266829071997359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193905888976177886047998239 290858833464266829071997359)
  ·
    refine ⟨436288250196400243607996039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290858833464266829071997359 436288250196400243607996039)
    ·
      refine ⟨654432375294600365411994059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436288250196400243607996039 654432375294600365411994059)
      ·
        refine ⟨981648562941900548117991089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654432375294600365411994059 981648562941900548117991089)
        ·
          refine ⟨736236422206425411088493317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981648562941900548117991089 736236422206425411088493317)
          ·
            refine ⟨138044329163704764579092497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 736236422206425411088493317 138044329163704764579092497)
            ·
              refine ⟨103533246872778573434319373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138044329163704764579092497 103533246872778573434319373)
              ·
                refine ⟨38824967577291965037869765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103533246872778573434319373 38824967577291965037869765)
                ·
                  refine ⟨7279681420742243444600581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38824967577291965037869765 7279681420742243444600581)
                  ·
                    refine ⟨1364940266389170645862609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7279681420742243444600581 1364940266389170645862609)
                    ·
                      rfl

theorem cell23_7974635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 4].length) (baseStart_7974635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974635 prefixEnd_7974635 := by exact prefixLift 7974635
  have htrace : WordTrace (prefixWord ++ tailWord_7974635) baseStart_7974635 baseEnd_7974635 := by
    simpa [prefixWord, tailWord_7974635, baseEnd_7974635] using wordTrace_append hprefix tailTrace_7974635
  have hstable : (prefixWord ++ tailWord_7974635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974635).length < 2 ^ (prefixWord ++ tailWord_7974635).sum := by decide
  have hdescent : baseEnd_7974635 < baseStart_7974635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974636 : List Nat := [2, 2, 1, 1, 2, 2, 6, 2, 1, 1, 3]
def baseStart_7974636 : Nat := 118140960795 + 7974636 * 2 ^ 59
def prefixEnd_7974636 : Nat := 4983230072969 + 3 ^ 40 * 7974636 * 2
def baseEnd_7974636 : Nat := 4094821312648166433675323

theorem tailTrace_7974636 : CollatzResearch.WordTrace tailWord_7974636 prefixEnd_7974636 4094821312648166433675323 := by
  unfold tailWord_7974636
  simp only [CollatzResearch.WordTrace]
  refine ⟨145429434968631603121391881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193905913291508804161855841 145429434968631603121391881)
  ·
    refine ⟨109072076226473702341043911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145429434968631603121391881 109072076226473702341043911)
    ·
      refine ⟨163608114339710553511565867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109072076226473702341043911 163608114339710553511565867)
      ·
        refine ⟨245412171509565830267348801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163608114339710553511565867 245412171509565830267348801)
        ·
          refine ⟨184059128632174372700511601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245412171509565830267348801 184059128632174372700511601)
          ·
            refine ⟨138044346474130779525383701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184059128632174372700511601 138044346474130779525383701)
            ·
              refine ⟨6470828740974880290252361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138044346474130779525383701 6470828740974880290252361)
              ·
                refine ⟨4853121555731160217689271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6470828740974880290252361 4853121555731160217689271)
                ·
                  refine ⟨7279682333596740326533907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4853121555731160217689271 7279682333596740326533907)
                  ·
                    refine ⟨10919523500395110489800861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7279682333596740326533907 10919523500395110489800861)
                    ·
                      refine ⟨4094821312648166433675323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10919523500395110489800861 4094821312648166433675323)
                      ·
                        rfl

theorem cell23_7974636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 1, 1, 3].length) (baseStart_7974636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974636 prefixEnd_7974636 := by exact prefixLift 7974636
  have htrace : WordTrace (prefixWord ++ tailWord_7974636) baseStart_7974636 baseEnd_7974636 := by
    simpa [prefixWord, tailWord_7974636, baseEnd_7974636] using wordTrace_append hprefix tailTrace_7974636
  have hstable : (prefixWord ++ tailWord_7974636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974636).length < 2 ^ (prefixWord ++ tailWord_7974636).sum := by decide
  have hdescent : baseEnd_7974636 < baseStart_7974636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974648 : List Nat := [2, 1, 2, 1, 1, 2, 2, 12]
def baseStart_7974648 : Nat := 118140960795 + 7974648 * 2 ^ 59
def prefixEnd_7974648 : Nat := 4983230072969 + 3 ^ 40 * 7974648 * 2
def baseEnd_7974648 : Nat := 151660276830222977286121

theorem tailTrace_7974648 : CollatzResearch.WordTrace tailWord_7974648 prefixEnd_7974648 151660276830222977286121 := by
  unfold tailWord_7974648
  simp only [CollatzResearch.WordTrace]
  refine ⟨145429653806609866146110299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193906205075479821528147065 145429653806609866146110299)
  ·
    refine ⟨218144480709914799219165449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145429653806609866146110299 218144480709914799219165449)
    ·
      refine ⟨163608360532436099414374087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218144480709914799219165449 163608360532436099414374087)
      ·
        refine ⟨245412540798654149121561131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163608360532436099414374087 245412540798654149121561131)
        ·
          refine ⟨368118811197981223682341697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245412540798654149121561131 368118811197981223682341697)
          ·
            refine ⟨276089108398485917761756273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368118811197981223682341697 276089108398485917761756273)
            ·
              refine ⟨207066831298864438321317205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276089108398485917761756273 207066831298864438321317205)
              ·
                refine ⟨151660276830222977286121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 207066831298864438321317205 151660276830222977286121)
                ·
                  rfl

theorem cell23_7974648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 12].length) (baseStart_7974648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974648 prefixEnd_7974648 := by exact prefixLift 7974648
  have htrace : WordTrace (prefixWord ++ tailWord_7974648) baseStart_7974648 baseEnd_7974648 := by
    simpa [prefixWord, tailWord_7974648, baseEnd_7974648] using wordTrace_append hprefix tailTrace_7974648
  have hstable : (prefixWord ++ tailWord_7974648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974648).length < 2 ^ (prefixWord ++ tailWord_7974648).sum := by decide
  have hdescent : baseEnd_7974648 < baseStart_7974648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974652 : List Nat := [2, 2, 2, 1, 3, 1, 1, 5, 2, 4]
def baseStart_7974652 : Nat := 118140960795 + 7974652 * 2 ^ 59
def prefixEnd_7974652 : Nat := 4983230072969 + 3 ^ 40 * 7974652 * 2
def baseEnd_7974652 : Nat := 1364943176112879457025083

theorem tailTrace_7974652 : CollatzResearch.WordTrace tailWord_7974652 prefixEnd_7974652 1364943176112879457025083 := by
  unfold tailWord_7974652
  simp only [CollatzResearch.WordTrace]
  refine ⟨145429726752602620487683105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193906302336803493983577473 145429726752602620487683105)
  ·
    refine ⟨109072295064451965365762329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145429726752602620487683105 109072295064451965365762329)
    ·
      refine ⟨81804221298338974024321747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109072295064451965365762329 81804221298338974024321747)
      ·
        refine ⟨122706331947508461036482621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81804221298338974024321747 122706331947508461036482621)
        ·
          refine ⟨46014874480315672888680983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122706331947508461036482621 46014874480315672888680983)
          ·
            refine ⟨69022311720473509333021475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46014874480315672888680983 69022311720473509333021475)
            ·
              refine ⟨103533467580710263999532213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69022311720473509333021475 103533467580710263999532213)
              ·
                refine ⟨9706262585691587249956145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103533467580710263999532213 9706262585691587249956145)
                ·
                  refine ⟨7279696939268690437467109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9706262585691587249956145 7279696939268690437467109)
                  ·
                    refine ⟨1364943176112879457025083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7279696939268690437467109 1364943176112879457025083)
                    ·
                      rfl

theorem cell23_7974652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_7974652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974652 prefixEnd_7974652 := by exact prefixLift 7974652
  have htrace : WordTrace (prefixWord ++ tailWord_7974652) baseStart_7974652 baseEnd_7974652 := by
    simpa [prefixWord, tailWord_7974652, baseEnd_7974652] using wordTrace_append hprefix tailTrace_7974652
  have hstable : (prefixWord ++ tailWord_7974652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974652).length < 2 ^ (prefixWord ++ tailWord_7974652).sum := by decide
  have hdescent : baseEnd_7974652 < baseStart_7974652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974655 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 4]
def baseStart_7974655 : Nat := 118140960795 + 7974655 * 2 ^ 59
def prefixEnd_7974655 : Nat := 4983230072969 + 3 ^ 40 * 7974655 * 2
def baseEnd_7974655 : Nat := 4094831068780601859337735

theorem tailTrace_7974655 : CollatzResearch.WordTrace tailWord_7974655 prefixEnd_7974655 4094831068780601859337735 := by
  unfold tailWord_7974655
  simp only [CollatzResearch.WordTrace]
  refine ⟨290859562924194372487725419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193906375282796248325150279 290859562924194372487725419)
  ·
    refine ⟨436289344386291558731588129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290859562924194372487725419 436289344386291558731588129)
    ·
      refine ⟨327217008289718669048691097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436289344386291558731588129 327217008289718669048691097)
      ·
        refine ⟨245412756217289001786518323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327217008289718669048691097 245412756217289001786518323)
        ·
          refine ⟨368119134325933502679777485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245412756217289001786518323 368119134325933502679777485)
          ·
            refine ⟨138044675372225063504916557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368119134325933502679777485 138044675372225063504916557)
            ·
              refine ⟨51766753264584398814343709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138044675372225063504916557 51766753264584398814343709)
              ·
                refine ⟨19412532474219149555378891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51766753264584398814343709 19412532474219149555378891)
                ·
                  refine ⟨29118798711328724333068337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19412532474219149555378891 29118798711328724333068337)
                  ·
                    refine ⟨21839099033496543249801253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29118798711328724333068337 21839099033496543249801253)
                    ·
                      refine ⟨4094831068780601859337735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21839099033496543249801253 4094831068780601859337735)
                      ·
                        rfl

theorem cell23_7974655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_7974655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974655 prefixEnd_7974655 := by exact prefixLift 7974655
  have htrace : WordTrace (prefixWord ++ tailWord_7974655) baseStart_7974655 baseEnd_7974655 := by
    simpa [prefixWord, tailWord_7974655, baseEnd_7974655] using wordTrace_append hprefix tailTrace_7974655
  have hstable : (prefixWord ++ tailWord_7974655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974655).length < 2 ^ (prefixWord ++ tailWord_7974655).sum := by decide
  have hdescent : baseEnd_7974655 < baseStart_7974655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974663 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 2, 3, 2]
def baseStart_7974663 : Nat := 118140960795 + 7974663 * 2 ^ 59
def prefixEnd_7974663 : Nat := 4983230072969 + 3 ^ 40 * 7974663 * 2
def baseEnd_7974663 : Nat := 4094835176625837828037699

theorem tailTrace_7974663 : CollatzResearch.WordTrace tailWord_7974663 prefixEnd_7974663 4094835176625837828037699 := by
  unfold tailWord_7974663
  simp only [CollatzResearch.WordTrace]
  refine ⟨290859854708165389854016643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193906569805443593236011095 290859854708165389854016643)
  ·
    refine ⟨436289782062248084781024965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290859854708165389854016643 436289782062248084781024965)
    ·
      refine ⟨81804334136671515896442181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 436289782062248084781024965 81804334136671515896442181)
      ·
        refine ⟨15338312650625909230582909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81804334136671515896442181 15338312650625909230582909)
        ·
          refine ⟨5751867243984715961468591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15338312650625909230582909 5751867243984715961468591)
          ·
            refine ⟨8627800865977073942202887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5751867243984715961468591 8627800865977073942202887)
            ·
              refine ⟨12941701298965610913304331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8627800865977073942202887 12941701298965610913304331)
              ·
                refine ⟨19412551948448416369956497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12941701298965610913304331 19412551948448416369956497)
                ·
                  refine ⟨14559413961336312277467373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19412551948448416369956497 14559413961336312277467373)
                  ·
                    refine ⟨5459780235501117104050265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14559413961336312277467373 5459780235501117104050265)
                    ·
                      refine ⟨4094835176625837828037699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5459780235501117104050265 4094835176625837828037699)
                      ·
                        rfl

theorem cell23_7974663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_7974663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974663 prefixEnd_7974663 := by exact prefixLift 7974663
  have htrace : WordTrace (prefixWord ++ tailWord_7974663) baseStart_7974663 baseEnd_7974663 := by
    simpa [prefixWord, tailWord_7974663, baseEnd_7974663] using wordTrace_append hprefix tailTrace_7974663
  have hstable : (prefixWord ++ tailWord_7974663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974663).length < 2 ^ (prefixWord ++ tailWord_7974663).sum := by decide
  have hdescent : baseEnd_7974663 < baseStart_7974663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974675 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 3]
def baseStart_7974675 : Nat := 118140960795 + 7974675 * 2 ^ 59
def prefixEnd_7974675 : Nat := 4983230072969 + 3 ^ 40 * 7974675 * 2
def baseEnd_7974675 : Nat := 4094841338393691781087643

theorem tailTrace_7974675 : CollatzResearch.WordTrace tailWord_7974675 prefixEnd_7974675 4094841338393691781087643 := by
  unfold tailWord_7974675
  simp only [CollatzResearch.WordTrace]
  refine ⟨290860292384121915903453479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193906861589414610602302319 290860292384121915903453479)
  ·
    refine ⟨436290438576182873855180219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290860292384121915903453479 436290438576182873855180219)
    ·
      refine ⟨654435657864274310782770329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436290438576182873855180219 654435657864274310782770329)
      ·
        refine ⟨490826743398205733087077747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654435657864274310782770329 490826743398205733087077747)
        ·
          refine ⟨736240115097308599630616621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490826743398205733087077747 736240115097308599630616621)
          ·
            refine ⟨276090043161490724861481233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736240115097308599630616621 276090043161490724861481233)
            ·
              refine ⟨207067532371118043646110925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276090043161490724861481233 207067532371118043646110925)
              ·
                refine ⟨77650324639169266367291597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207067532371118043646110925 77650324639169266367291597)
                ·
                  refine ⟨29118871739688474887734349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77650324639169266367291597 29118871739688474887734349)
                  ·
                    refine ⟨10919576902383178082900381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29118871739688474887734349 10919576902383178082900381)
                    ·
                      refine ⟨4094841338393691781087643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10919576902383178082900381 4094841338393691781087643)
                      ·
                        rfl

theorem cell23_7974675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 3].length) (baseStart_7974675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974675 prefixEnd_7974675 := by exact prefixLift 7974675
  have htrace : WordTrace (prefixWord ++ tailWord_7974675) baseStart_7974675 baseEnd_7974675 := by
    simpa [prefixWord, tailWord_7974675, baseEnd_7974675] using wordTrace_append hprefix tailTrace_7974675
  have hstable : (prefixWord ++ tailWord_7974675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974675).length < 2 ^ (prefixWord ++ tailWord_7974675).sum := by decide
  have hdescent : baseEnd_7974675 < baseStart_7974675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974679 : List Nat := [1, 1, 3, 4, 2, 2, 1, 3, 1, 2, 3]
def baseStart_7974679 : Nat := 118140960795 + 7974679 * 2 ^ 59
def prefixEnd_7974679 : Nat := 4983230072969 + 3 ^ 40 * 7974679 * 2
def baseEnd_7974679 : Nat := 4094843392316309765437625

theorem tailTrace_7974679 : CollatzResearch.WordTrace tailWord_7974679 prefixEnd_7974679 4094843392316309765437625 := by
  unfold tailWord_7974679
  simp only [CollatzResearch.WordTrace]
  refine ⟨290860438276107424586599091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193906958850738283057732727 290860438276107424586599091)
  ·
    refine ⟨436290657414161136879898637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290860438276107424586599091 436290657414161136879898637)
    ·
      refine ⟨163608996530310426329961989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436290657414161136879898637 163608996530310426329961989)
      ·
        refine ⟨30676686849433204936867873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163608996530310426329961989 30676686849433204936867873)
        ·
          refine ⟨23007515137074903702650905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30676686849433204936867873 23007515137074903702650905)
          ·
            refine ⟨17255636352806177776988179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23007515137074903702650905 17255636352806177776988179)
            ·
              refine ⟨25883454529209266665482269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17255636352806177776988179 25883454529209266665482269)
              ·
                refine ⟨9706295448453474999555851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25883454529209266665482269 9706295448453474999555851)
                ·
                  refine ⟨14559443172680212499333777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9706295448453474999555851 14559443172680212499333777)
                  ·
                    refine ⟨10919582379510159374500333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14559443172680212499333777 10919582379510159374500333)
                    ·
                      refine ⟨4094843392316309765437625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10919582379510159374500333 4094843392316309765437625)
                      ·
                        rfl

theorem cell23_7974679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_7974679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974679 prefixEnd_7974679 := by exact prefixLift 7974679
  have htrace : WordTrace (prefixWord ++ tailWord_7974679) baseStart_7974679 baseEnd_7974679 := by
    simpa [prefixWord, tailWord_7974679, baseEnd_7974679] using wordTrace_append hprefix tailTrace_7974679
  have hstable : (prefixWord ++ tailWord_7974679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974679).length < 2 ^ (prefixWord ++ tailWord_7974679).sum := by decide
  have hdescent : baseEnd_7974679 < baseStart_7974679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974836 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_7974836 : Nat := 118140960795 + 7974836 * 2 ^ 59
def prefixEnd_7974836 : Nat := 4983230072969 + 3 ^ 40 * 7974836 * 2
def baseEnd_7974836 : Nat := 1364974669593021883724801

theorem tailTrace_7974836 : CollatzResearch.WordTrace tailWord_7974836 prefixEnd_7974836 1364974669593021883724801 := by
  unfold tailWord_7974836
  simp only [CollatzResearch.WordTrace]
  refine ⟨145433082268269320200032181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193910776357692426933376241 145433082268269320200032181)
  ·
    refine ⟨13634351462650248768753017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145433082268269320200032181 13634351462650248768753017)
    ·
      refine ⟨10225763596987686576564763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13634351462650248768753017 10225763596987686576564763)
      ·
        refine ⟨15338645395481529864847145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10225763596987686576564763 15338645395481529864847145)
        ·
          refine ⟨11503984046611147398635359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15338645395481529864847145 11503984046611147398635359)
          ·
            refine ⟨17255976069916721097953039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11503984046611147398635359 17255976069916721097953039)
            ·
              refine ⟨25883964104875081646929559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17255976069916721097953039 25883964104875081646929559)
              ·
                refine ⟨38825946157312622470394339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25883964104875081646929559 38825946157312622470394339)
                ·
                  refine ⟨58238919235968933705591509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38825946157312622470394339 58238919235968933705591509)
                  ·
                    refine ⟨1364974669593021883724801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58238919235968933705591509 1364974669593021883724801)
                    ·
                      rfl

theorem cell23_7974836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_7974836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974836 prefixEnd_7974836 := by exact prefixLift 7974836
  have htrace : WordTrace (prefixWord ++ tailWord_7974836) baseStart_7974836 baseEnd_7974836 := by
    simpa [prefixWord, tailWord_7974836, baseEnd_7974836] using wordTrace_append hprefix tailTrace_7974836
  have hstable : (prefixWord ++ tailWord_7974836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974836).length < 2 ^ (prefixWord ++ tailWord_7974836).sum := by decide
  have hdescent : baseEnd_7974836 < baseStart_7974836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974862 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 8]
def baseStart_7974862 : Nat := 118140960795 + 7974862 * 2 ^ 59
def prefixEnd_7974862 : Nat := 4983230072969 + 3 ^ 40 * 7974862 * 2
def baseEnd_7974862 : Nat := 454993039919564727716587

theorem tailTrace_7974862 : CollatzResearch.WordTrace tailWord_7974862 prefixEnd_7974862 454993039919564727716587 := by
  unfold tailWord_7974862
  simp only [CollatzResearch.WordTrace]
  refine ⟨36358389104305555855063855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193911408556296297893673893 36358389104305555855063855)
  ·
    refine ⟨54537583656458333782595783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36358389104305555855063855 54537583656458333782595783)
    ·
      refine ⟨81806375484687500673893675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54537583656458333782595783 81806375484687500673893675)
      ·
        refine ⟨122709563227031251010840513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81806375484687500673893675 122709563227031251010840513)
        ·
          refine ⟨92032172420273438258130385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122709563227031251010840513 92032172420273438258130385)
          ·
            refine ⟨69024129315205078693597789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92032172420273438258130385 69024129315205078693597789)
            ·
              refine ⟨25884048493201904510099171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69024129315205078693597789 25884048493201904510099171)
              ·
                refine ⟨38826072739802856765148757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25884048493201904510099171 38826072739802856765148757)
                ·
                  refine ⟨454993039919564727716587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38826072739802856765148757 454993039919564727716587)
                  ·
                    rfl

theorem cell23_7974862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_7974862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974862 prefixEnd_7974862 := by exact prefixLift 7974862
  have htrace : WordTrace (prefixWord ++ tailWord_7974862) baseStart_7974862 baseEnd_7974862 := by
    simpa [prefixWord, tailWord_7974862, baseEnd_7974862] using wordTrace_append hprefix tailTrace_7974862
  have hstable : (prefixWord ++ tailWord_7974862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974862).length < 2 ^ (prefixWord ++ tailWord_7974862).sum := by decide
  have hdescent : baseEnd_7974862 < baseStart_7974862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974892 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 3, 5]
def baseStart_7974892 : Nat := 118140960795 + 7974892 * 2 ^ 59
def prefixEnd_7974892 : Nat := 4983230072969 + 3 ^ 40 * 7974892 * 2
def baseEnd_7974892 : Nat := 1364984254565239144024715

theorem tailTrace_7974892 : CollatzResearch.WordTrace tailWord_7974892 prefixEnd_7974892 1364984254565239144024715 := by
  unfold tailWord_7974892
  simp only [CollatzResearch.WordTrace]
  refine ⟨145434103512167880982051465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193912138016223841309401953 145434103512167880982051465)
  ·
    refine ⟨109075577634125910736538599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145434103512167880982051465 109075577634125910736538599)
    ·
      refine ⟨163613366451188866104807899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109075577634125910736538599 163613366451188866104807899)
      ·
        refine ⟨245420049676783299157211849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163613366451188866104807899 245420049676783299157211849)
        ·
          refine ⟨184065037257587474367908887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245420049676783299157211849 184065037257587474367908887)
          ·
            refine ⟨276097555886381211551863331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184065037257587474367908887 276097555886381211551863331)
            ·
              refine ⟨414146333829571817327794997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276097555886381211551863331 414146333829571817327794997)
              ·
                refine ⟨38826218796522357874480781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 414146333829571817327794997 38826218796522357874480781)
                ·
                  refine ⟨14559832048695884202930293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38826218796522357874480781 14559832048695884202930293)
                  ·
                    refine ⟨1364984254565239144024715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14559832048695884202930293 1364984254565239144024715)
                    ·
                      rfl

theorem cell23_7974892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_7974892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974892 prefixEnd_7974892 := by exact prefixLift 7974892
  have htrace : WordTrace (prefixWord ++ tailWord_7974892) baseStart_7974892 baseEnd_7974892 := by
    simpa [prefixWord, tailWord_7974892, baseEnd_7974892] using wordTrace_append hprefix tailTrace_7974892
  have hstable : (prefixWord ++ tailWord_7974892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974892).length < 2 ^ (prefixWord ++ tailWord_7974892).sum := by decide
  have hdescent : baseEnd_7974892 < baseStart_7974892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974899 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 6, 3, 2]
def baseStart_7974899 : Nat := 118140960795 + 7974899 * 2 ^ 59
def prefixEnd_7974899 : Nat := 4983230072969 + 3 ^ 40 * 7974899 * 2
def baseEnd_7974899 : Nat := 4094956358060298904686613

theorem tailTrace_7974899 : CollatzResearch.WordTrace tailWord_7974899 prefixEnd_7974899 4094956358060298904686613 := by
  unfold tailWord_7974899
  simp only [CollatzResearch.WordTrace]
  refine ⟨290868462335310402159607751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193912308223540268106405167 290868462335310402159607751)
  ·
    refine ⟨436302693502965603239411627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290868462335310402159607751 436302693502965603239411627)
    ·
      refine ⟨654454040254448404859117441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436302693502965603239411627 654454040254448404859117441)
      ·
        refine ⟨490840530190836303644338081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654454040254448404859117441 490840530190836303644338081)
        ·
          refine ⟨368130397643127227733253561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490840530190836303644338081 368130397643127227733253561)
          ·
            refine ⟨276097798232345420799940171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368130397643127227733253561 276097798232345420799940171)
            ·
              refine ⟨414146697348518131199910257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276097798232345420799940171 414146697348518131199910257)
              ·
                refine ⟨310610023011388598399932693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414146697348518131199910257 310610023011388598399932693)
                ·
                  refine ⟨14559844828658840549996845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 310610023011388598399932693 14559844828658840549996845)
                  ·
                    refine ⟨5459941810747065206248817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14559844828658840549996845 5459941810747065206248817)
                    ·
                      refine ⟨4094956358060298904686613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5459941810747065206248817 4094956358060298904686613)
                      ·
                        rfl

theorem cell23_7974899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 3, 2].length) (baseStart_7974899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974899 prefixEnd_7974899 := by exact prefixLift 7974899
  have htrace : WordTrace (prefixWord ++ tailWord_7974899) baseStart_7974899 baseEnd_7974899 := by
    simpa [prefixWord, tailWord_7974899, baseEnd_7974899] using wordTrace_append hprefix tailTrace_7974899
  have hstable : (prefixWord ++ tailWord_7974899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974899).length < 2 ^ (prefixWord ++ tailWord_7974899).sum := by decide
  have hdescent : baseEnd_7974899 < baseStart_7974899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974909 : List Nat := [1, 4, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_7974909 : Nat := 118140960795 + 7974909 * 2 ^ 59
def prefixEnd_7974909 : Nat := 4983230072969 + 3 ^ 40 * 7974909 * 2
def baseEnd_7974909 : Nat := 1364987164288947955187189

theorem tailTrace_7974909 : CollatzResearch.WordTrace tailWord_7974909 prefixEnd_7974909 1364987164288947955187189 := by
  unfold tailWord_7974909
  simp only [CollatzResearch.WordTrace]
  refine ⟨290868827065274173867471781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193912551376849449244981187 290868827065274173867471781)
  ·
    refine ⟨54537905074738907600150959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290868827065274173867471781 54537905074738907600150959)
    ·
      refine ⟨81806857612108361400226439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54537905074738907600150959 81806857612108361400226439)
      ·
        refine ⟨122710286418162542100339659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81806857612108361400226439 122710286418162542100339659)
        ·
          refine ⟨184065429627243813150509489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122710286418162542100339659 184065429627243813150509489)
          ·
            refine ⟨138049072220432859862882117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184065429627243813150509489 138049072220432859862882117)
            ·
              refine ⟨25884201041331161224290397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138049072220432859862882117 25884201041331161224290397)
              ·
                refine ⟨9706575390499185459108899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25884201041331161224290397 9706575390499185459108899)
                ·
                  refine ⟨14559863085748778188663349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9706575390499185459108899 14559863085748778188663349)
                  ·
                    refine ⟨1364987164288947955187189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14559863085748778188663349 1364987164288947955187189)
                    ·
                      rfl

theorem cell23_7974909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_7974909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974909 prefixEnd_7974909 := by exact prefixLift 7974909
  have htrace : WordTrace (prefixWord ++ tailWord_7974909) baseStart_7974909 baseEnd_7974909 := by
    simpa [prefixWord, tailWord_7974909, baseEnd_7974909] using wordTrace_append hprefix tailTrace_7974909
  have hstable : (prefixWord ++ tailWord_7974909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974909).length < 2 ^ (prefixWord ++ tailWord_7974909).sum := by decide
  have hdescent : baseEnd_7974909 < baseStart_7974909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974969 : List Nat := [1, 2, 1, 5, 4, 10]
def baseStart_7974969 : Nat := 118140960795 + 7974969 * 2 ^ 59
def prefixEnd_7974969 : Nat := 4983230072969 + 3 ^ 40 * 7974969 * 2
def baseEnd_7974969 : Nat := 16851820171630097246137

theorem tailTrace_7974969 : CollatzResearch.WordTrace tailWord_7974969 prefixEnd_7974969 16851820171630097246137 := by
  unfold tailWord_7974969
  simp only [CollatzResearch.WordTrace]
  refine ⟨290871015445056804114655961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193914010296704536076437307 290871015445056804114655961)
  ·
    refine ⟨218153261583792603085991971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290871015445056804114655961 218153261583792603085991971)
    ·
      refine ⟨327229892375688904628987957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218153261583792603085991971 327229892375688904628987957)
      ·
        refine ⟨30677802410220834808967621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 327229892375688904628987957 30677802410220834808967621)
        ·
          refine ⟨5752087951916406526681429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30677802410220834808967621 5752087951916406526681429)
          ·
            refine ⟨16851820171630097246137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5752087951916406526681429 16851820171630097246137)
            ·
              rfl

theorem cell23_7974969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 10].length) (baseStart_7974969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974969 prefixEnd_7974969 := by exact prefixLift 7974969
  have htrace : WordTrace (prefixWord ++ tailWord_7974969) baseStart_7974969 baseEnd_7974969 := by
    simpa [prefixWord, tailWord_7974969, baseEnd_7974969] using wordTrace_append hprefix tailTrace_7974969
  have hstable : (prefixWord ++ tailWord_7974969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974969).length < 2 ^ (prefixWord ++ tailWord_7974969).sum := by decide
  have hdescent : baseEnd_7974969 < baseStart_7974969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974974 : List Nat := [4, 2, 1, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_7974974 : Nat := 118140960795 + 7974974 * 2 ^ 59
def prefixEnd_7974974 : Nat := 4983230072969 + 3 ^ 40 * 7974974 * 2
def baseEnd_7974974 : Nat := 4094994869109386111248769

theorem tailTrace_7974974 : CollatzResearch.WordTrace tailWord_7974974 prefixEnd_7974974 4094994869109386111248769 := by
  unfold tailWord_7974974
  simp only [CollatzResearch.WordTrace]
  refine ⟨36358899726254836246073497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193914131873359126645725317 36358899726254836246073497)
  ·
    refine ⟨27269174794691127184555123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36358899726254836246073497 27269174794691127184555123)
    ·
      refine ⟨40903762192036690776832685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27269174794691127184555123 40903762192036690776832685)
      ·
        refine ⟨15338910822013759041312257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40903762192036690776832685 15338910822013759041312257)
        ·
          refine ⟨11504183116510319280984193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15338910822013759041312257 11504183116510319280984193)
          ·
            refine ⟨8628137337382739460738145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11504183116510319280984193 8628137337382739460738145)
            ·
              refine ⟨6471103003037054595553609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8628137337382739460738145 6471103003037054595553609)
              ·
                refine ⟨4853327252277790946665207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6471103003037054595553609 4853327252277790946665207)
                ·
                  refine ⟨7279990878416686419997811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4853327252277790946665207 7279990878416686419997811)
                  ·
                    refine ⟨10919986317625029629996717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7279990878416686419997811 10919986317625029629996717)
                    ·
                      refine ⟨4094994869109386111248769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10919986317625029629996717 4094994869109386111248769)
                      ·
                        rfl

theorem cell23_7974974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_7974974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974974 prefixEnd_7974974 := by exact prefixLift 7974974
  have htrace : WordTrace (prefixWord ++ tailWord_7974974) baseStart_7974974 baseEnd_7974974 := by
    simpa [prefixWord, tailWord_7974974, baseEnd_7974974] using wordTrace_append hprefix tailTrace_7974974
  have hstable : (prefixWord ++ tailWord_7974974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974974).length < 2 ^ (prefixWord ++ tailWord_7974974).sum := by decide
  have hdescent : baseEnd_7974974 < baseStart_7974974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974992 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 5]
def baseStart_7974992 : Nat := 118140960795 + 7974992 * 2 ^ 59
def prefixEnd_7974992 : Nat := 4983230072969 + 3 ^ 40 * 7974992 * 2
def baseEnd_7974992 : Nat := 4095004111761167040823685

theorem tailTrace_7974992 : CollatzResearch.WordTrace tailWord_7974992 prefixEnd_7974992 4095004111761167040823685 := by
  unfold tailWord_7974992
  simp only [CollatzResearch.WordTrace]
  refine ⟨145435927161986739521371615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193914569549315652695162153 145435927161986739521371615)
  ·
    refine ⟨218153890742980109282057423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145435927161986739521371615 218153890742980109282057423)
    ·
      refine ⟨327230836114470163923086135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218153890742980109282057423 327230836114470163923086135)
      ·
        refine ⟨490846254171705245884629203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327230836114470163923086135 490846254171705245884629203)
        ·
          refine ⟨736269381257557868826943805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490846254171705245884629203 736269381257557868826943805)
          ·
            refine ⟨276101017971584200810103927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736269381257557868826943805 276101017971584200810103927)
            ·
              refine ⟨414151526957376301215155891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276101017971584200810103927 414151526957376301215155891)
              ·
                refine ⟨621227290436064451822733837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414151526957376301215155891 621227290436064451822733837)
                ·
                  refine ⟨232960233913524169433525189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 621227290436064451822733837 232960233913524169433525189)
                  ·
                    refine ⟨43680043858785781768785973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 232960233913524169433525189 43680043858785781768785973)
                    ·
                      refine ⟨4095004111761167040823685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43680043858785781768785973 4095004111761167040823685)
                      ·
                        rfl

theorem cell23_7974992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_7974992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974992 prefixEnd_7974992 := by exact prefixLift 7974992
  have htrace : WordTrace (prefixWord ++ tailWord_7974992) baseStart_7974992 baseEnd_7974992 := by
    simpa [prefixWord, tailWord_7974992, baseEnd_7974992] using wordTrace_append hprefix tailTrace_7974992
  have hstable : (prefixWord ++ tailWord_7974992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974992).length < 2 ^ (prefixWord ++ tailWord_7974992).sum := by decide
  have hdescent : baseEnd_7974992 < baseStart_7974992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7974996 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_7974996 : Nat := 118140960795 + 7974996 * 2 ^ 59
def prefixEnd_7974996 : Nat := 4983230072969 + 3 ^ 40 * 7974996 * 2
def baseEnd_7974996 : Nat := 4095006165683785025173667

theorem tailTrace_7974996 : CollatzResearch.WordTrace tailWord_7974996 prefixEnd_7974996 4095006165683785025173667 := by
  unfold tailWord_7974996
  simp only [CollatzResearch.WordTrace]
  refine ⟨145436000107979493862944421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193914666810639325150592561 145436000107979493862944421)
  ·
    refine ⟨27269250020246155099302079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145436000107979493862944421 27269250020246155099302079)
    ·
      refine ⟨40903875030369232648953119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27269250020246155099302079 40903875030369232648953119)
      ·
        refine ⟨61355812545553848973429679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40903875030369232648953119 61355812545553848973429679)
        ·
          refine ⟨92033718818330773460144519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61355812545553848973429679 92033718818330773460144519)
          ·
            refine ⟨138050578227496160190216779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92033718818330773460144519 138050578227496160190216779)
            ·
              refine ⟨207075867341244240285325169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138050578227496160190216779 207075867341244240285325169)
              ·
                refine ⟨155306900505933180213993877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207075867341244240285325169 155306900505933180213993877)
                ·
                  refine ⟨7280010961215617822530963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155306900505933180213993877 7280010961215617822530963)
                  ·
                    refine ⟨10920016441823426733796445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7280010961215617822530963 10920016441823426733796445)
                    ·
                      refine ⟨4095006165683785025173667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10920016441823426733796445 4095006165683785025173667)
                      ·
                        rfl

theorem cell23_7974996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_7974996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7974996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7974996 prefixEnd_7974996 := by exact prefixLift 7974996
  have htrace : WordTrace (prefixWord ++ tailWord_7974996) baseStart_7974996 baseEnd_7974996 := by
    simpa [prefixWord, tailWord_7974996, baseEnd_7974996] using wordTrace_append hprefix tailTrace_7974996
  have hstable : (prefixWord ++ tailWord_7974996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7974996).length < 2 ^ (prefixWord ++ tailWord_7974996).sum := by decide
  have hdescent : baseEnd_7974996 < baseStart_7974996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7974996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975023 : List Nat := [1, 1, 2, 1, 3, 5, 1, 3, 1, 3, 2]
def baseStart_7975023 : Nat := 118140960795 + 7975023 * 2 ^ 59
def prefixEnd_7975023 : Nat := 4983230072969 + 3 ^ 40 * 7975023 * 2
def baseEnd_7975023 : Nat := 4095020029661456419536043

theorem tailTrace_7975023 : CollatzResearch.WordTrace tailWord_7975023 prefixEnd_7975023 4095020029661456419536043 := by
  unfold tailWord_7975023
  simp only [CollatzResearch.WordTrace]
  refine ⟨290872984986861171337121723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193915323324574114224747815 290872984986861171337121723)
  ·
    refine ⟨436309477480291757005682585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290872984986861171337121723 436309477480291757005682585)
    ·
      refine ⟨327232108110218817754261939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436309477480291757005682585 327232108110218817754261939)
      ·
        refine ⟨490848162165328226631392909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327232108110218817754261939 490848162165328226631392909)
        ·
          refine ⟨184068060811998084986772341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490848162165328226631392909 184068060811998084986772341)
          ·
            refine ⟨17256380701124820467509907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184068060811998084986772341 17256380701124820467509907)
            ·
              refine ⟨25884571051687230701264861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17256380701124820467509907 25884571051687230701264861)
              ·
                refine ⟨9706714144382711512974323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25884571051687230701264861 9706714144382711512974323)
                ·
                  refine ⟨14560071216574067269461485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9706714144382711512974323 14560071216574067269461485)
                  ·
                    refine ⟨5460026706215275226048057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14560071216574067269461485 5460026706215275226048057)
                    ·
                      refine ⟨4095020029661456419536043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460026706215275226048057 4095020029661456419536043)
                      ·
                        rfl

theorem cell23_7975023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 3, 2].length) (baseStart_7975023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975023 prefixEnd_7975023 := by exact prefixLift 7975023
  have htrace : WordTrace (prefixWord ++ tailWord_7975023) baseStart_7975023 baseEnd_7975023 := by
    simpa [prefixWord, tailWord_7975023, baseEnd_7975023] using wordTrace_append hprefix tailTrace_7975023
  have hstable : (prefixWord ++ tailWord_7975023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975023).length < 2 ^ (prefixWord ++ tailWord_7975023).sum := by decide
  have hdescent : baseEnd_7975023 < baseStart_7975023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975030 : List Nat := [5, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_7975030 : Nat := 118140960795 + 7975030 * 2 ^ 59
def prefixEnd_7975030 : Nat := 4983230072969 + 3 ^ 40 * 7975030 * 2
def baseEnd_7975030 : Nat := 4095023624026037892148511

theorem tailTrace_7975030 : CollatzResearch.WordTrace tailWord_7975030 prefixEnd_7975030 4095023624026037892148511 := by
  unfold tailWord_7975030
  simp only [CollatzResearch.WordTrace]
  refine ⟨18179577518614738220789159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193915493531890541021751029 18179577518614738220789159)
  ·
    refine ⟨27269366277922107331183739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18179577518614738220789159 27269366277922107331183739)
    ·
      refine ⟨40904049416883160996775609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27269366277922107331183739 40904049416883160996775609)
      ·
        refine ⟨30678037062662370747581707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40904049416883160996775609 30678037062662370747581707)
        ·
          refine ⟨46017055593993556121372561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30678037062662370747581707 46017055593993556121372561)
          ·
            refine ⟨34512791695495167091029421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46017055593993556121372561 34512791695495167091029421)
            ·
              refine ⟨12942296885810687659136033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34512791695495167091029421 12942296885810687659136033)
              ·
                refine ⟨9706722664358015744352025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12942296885810687659136033 9706722664358015744352025)
                ·
                  refine ⟨7280041998268511808264019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9706722664358015744352025 7280041998268511808264019)
                  ·
                    refine ⟨10920062997402767712396029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7280041998268511808264019 10920062997402767712396029)
                    ·
                      refine ⟨4095023624026037892148511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10920062997402767712396029 4095023624026037892148511)
                      ·
                        rfl

theorem cell23_7975030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_7975030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975030 prefixEnd_7975030 := by exact prefixLift 7975030
  have htrace : WordTrace (prefixWord ++ tailWord_7975030) baseStart_7975030 baseEnd_7975030 := by
    simpa [prefixWord, tailWord_7975030, baseEnd_7975030] using wordTrace_append hprefix tailTrace_7975030
  have hstable : (prefixWord ++ tailWord_7975030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975030).length < 2 ^ (prefixWord ++ tailWord_7975030).sum := by decide
  have hdescent : baseEnd_7975030 < baseStart_7975030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975049 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 2, 2, 4]
def baseStart_7975049 : Nat := 118140960795 + 7975049 * 2 ^ 59
def prefixEnd_7975049 : Nat := 4983230072969 + 3 ^ 40 * 7975049 * 2
def baseEnd_7975049 : Nat := 4095033380158473317810923

theorem tailTrace_7975049 : CollatzResearch.WordTrace tailWord_7975049 prefixEnd_7975049 4095033380158473317810923 := by
  unfold tailWord_7975049
  simp only [CollatzResearch.WordTrace]
  refine ⟨290873933284766977777568201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193915955523177985185045467 290873933284766977777568201)
  ·
    refine ⟨218155449963575233333176151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290873933284766977777568201 218155449963575233333176151)
    ·
      refine ⟨327233174945362849999764227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218155449963575233333176151 327233174945362849999764227)
      ·
        refine ⟨490849762418044274999646341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327233174945362849999764227 490849762418044274999646341)
        ·
          refine ⟨92034330453383301562433689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490849762418044274999646341 92034330453383301562433689)
          ·
            refine ⟨69025747840037476171825267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92034330453383301562433689 69025747840037476171825267)
            ·
              refine ⟨103538621760056214257737901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69025747840037476171825267 103538621760056214257737901)
              ·
                refine ⟨38826983160021080346651713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103538621760056214257737901 38826983160021080346651713)
                ·
                  refine ⟨29120237370015810259988785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38826983160021080346651713 29120237370015810259988785)
                  ·
                    refine ⟨21840178027511857694991589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29120237370015810259988785 21840178027511857694991589)
                    ·
                      refine ⟨4095033380158473317810923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21840178027511857694991589 4095033380158473317810923)
                      ·
                        rfl

theorem cell23_7975049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_7975049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975049 prefixEnd_7975049 := by exact prefixLift 7975049
  have htrace : WordTrace (prefixWord ++ tailWord_7975049) baseStart_7975049 baseEnd_7975049 := by
    simpa [prefixWord, tailWord_7975049, baseEnd_7975049] using wordTrace_append hprefix tailTrace_7975049
  have hstable : (prefixWord ++ tailWord_7975049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975049).length < 2 ^ (prefixWord ++ tailWord_7975049).sum := by decide
  have hdescent : baseEnd_7975049 < baseStart_7975049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975096 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 2, 5, 2]
def baseStart_7975096 : Nat := 118140960795 + 7975096 * 2 ^ 59
def prefixEnd_7975096 : Nat := 4983230072969 + 3 ^ 40 * 7975096 * 2
def baseEnd_7975096 : Nat := 4095057513749234633923207

theorem tailTrace_7975096 : CollatzResearch.WordTrace tailWord_7975096 prefixEnd_7975096 4095057513749234633923207 := by
  unfold tailWord_7975096
  simp only [CollatzResearch.WordTrace]
  refine ⟨145437823757798352402264571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193917098343731136536352761 145437823757798352402264571)
  ·
    refine ⟨218156735636697528603396857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145437823757798352402264571 218156735636697528603396857)
    ·
      refine ⟨163617551727523146452547643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218156735636697528603396857 163617551727523146452547643)
      ·
        refine ⟨245426327591284719678821465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163617551727523146452547643 245426327591284719678821465)
        ·
          refine ⟨184069745693463539759116099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245426327591284719678821465 184069745693463539759116099)
          ·
            refine ⟨276104618540195309638674149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184069745693463539759116099 276104618540195309638674149)
            ·
              refine ⟨51769615976286620557251403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276104618540195309638674149 51769615976286620557251403)
              ·
                refine ⟨77654423964429930835877105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51769615976286620557251403 77654423964429930835877105)
                ·
                  refine ⟨58240817973322448126907829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77654423964429930835877105 58240817973322448126907829)
                  ·
                    refine ⟨5460076684998979511897609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58240817973322448126907829 5460076684998979511897609)
                    ·
                      refine ⟨4095057513749234633923207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460076684998979511897609 4095057513749234633923207)
                      ·
                        rfl

theorem cell23_7975096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 5, 2].length) (baseStart_7975096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975096 prefixEnd_7975096 := by exact prefixLift 7975096
  have htrace : WordTrace (prefixWord ++ tailWord_7975096) baseStart_7975096 baseEnd_7975096 := by
    simpa [prefixWord, tailWord_7975096, baseEnd_7975096] using wordTrace_append hprefix tailTrace_7975096
  have hstable : (prefixWord ++ tailWord_7975096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975096).length < 2 ^ (prefixWord ++ tailWord_7975096).sum := by decide
  have hdescent : baseEnd_7975096 < baseStart_7975096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975099 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 5]
def baseStart_7975099 : Nat := 118140960795 + 7975099 * 2 ^ 59
def prefixEnd_7975099 : Nat := 4983230072969 + 3 ^ 40 * 7975099 * 2
def baseEnd_7975099 : Nat := 4095059054191198122185693

theorem tailTrace_7975099 : CollatzResearch.WordTrace tailWord_7975099 prefixEnd_7975099 4095059054191198122185693 := by
  unfold tailWord_7975099
  simp only [CollatzResearch.WordTrace]
  refine ⟨290875756934585836316888351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193917171289723890877925567 290875756934585836316888351)
  ·
    refine ⟨436313635401878754475332527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290875756934585836316888351 436313635401878754475332527)
    ·
      refine ⟨654470453102818131712998791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436313635401878754475332527 654470453102818131712998791)
      ·
        refine ⟨981705679654227197569498187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654470453102818131712998791 981705679654227197569498187)
        ·
          refine ⟨1472558519481340796354247281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981705679654227197569498187 1472558519481340796354247281)
          ·
            refine ⟨1104418889611005597265685461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472558519481340796354247281 1104418889611005597265685461)
            ·
              refine ⟨25884817725257943685914503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1104418889611005597265685461 25884817725257943685914503)
              ·
                refine ⟨38827226587886915528871755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25884817725257943685914503 38827226587886915528871755)
                ·
                  refine ⟨58240839881830373293307633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38827226587886915528871755 58240839881830373293307633)
                  ·
                    refine ⟨43680629911372779969980725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58240839881830373293307633 43680629911372779969980725)
                    ·
                      refine ⟨4095059054191198122185693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43680629911372779969980725 4095059054191198122185693)
                      ·
                        rfl

theorem cell23_7975099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 5].length) (baseStart_7975099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975099 prefixEnd_7975099 := by exact prefixLift 7975099
  have htrace : WordTrace (prefixWord ++ tailWord_7975099) baseStart_7975099 baseEnd_7975099 := by
    simpa [prefixWord, tailWord_7975099, baseEnd_7975099] using wordTrace_append hprefix tailTrace_7975099
  have hstable : (prefixWord ++ tailWord_7975099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975099).length < 2 ^ (prefixWord ++ tailWord_7975099).sum := by decide
  have hdescent : baseEnd_7975099 < baseStart_7975099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975109 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_7975109 : Nat := 118140960795 + 7975109 * 2 ^ 59
def prefixEnd_7975109 : Nat := 4983230072969 + 3 ^ 40 * 7975109 * 2
def baseEnd_7975109 : Nat := 4095064188997743083060647

theorem tailTrace_7975109 : CollatzResearch.WordTrace tailWord_7975109 prefixEnd_7975109 4095064188997743083060647 := by
  unfold tailWord_7975109
  simp only [CollatzResearch.WordTrace]
  refine ⟨290876121664549608024752381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193917414443033072016501587 290876121664549608024752381)
  ·
    refine ⟨109078545624206103009282143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290876121664549608024752381 109078545624206103009282143)
    ·
      refine ⟨163617818436309154513923215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109078545624206103009282143 163617818436309154513923215)
      ·
        refine ⟨245426727654463731770884823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163617818436309154513923215 245426727654463731770884823)
        ·
          refine ⟨368140091481695597656327235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245426727654463731770884823 368140091481695597656327235)
          ·
            refine ⟨552210137222543396484490853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368140091481695597656327235 552210137222543396484490853)
            ·
              refine ⟨103539400729226886840842035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 552210137222543396484490853 103539400729226886840842035)
              ·
                refine ⟨155309101093840330261263053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103539400729226886840842035 155309101093840330261263053)
                ·
                  refine ⟨58240912910190123847973645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155309101093840330261263053 58240912910190123847973645)
                  ·
                    refine ⟨21840342341321296442990117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58240912910190123847973645 21840342341321296442990117)
                    ·
                      refine ⟨4095064188997743083060647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21840342341321296442990117 4095064188997743083060647)
                      ·
                        rfl

theorem cell23_7975109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_7975109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975109 prefixEnd_7975109 := by exact prefixLift 7975109
  have htrace : WordTrace (prefixWord ++ tailWord_7975109) baseStart_7975109 baseEnd_7975109 := by
    simpa [prefixWord, tailWord_7975109, baseEnd_7975109] using wordTrace_append hprefix tailTrace_7975109
  have hstable : (prefixWord ++ tailWord_7975109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975109).length < 2 ^ (prefixWord ++ tailWord_7975109).sum := by decide
  have hdescent : baseEnd_7975109 < baseStart_7975109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975143 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_7975143 : Nat := 118140960795 + 7975143 * 2 ^ 59
def prefixEnd_7975143 : Nat := 4983230072969 + 3 ^ 40 * 7975143 * 2
def baseEnd_7975143 : Nat := 4095081647339995950035491

theorem tailTrace_7975143 : CollatzResearch.WordTrace tailWord_7975143 prefixEnd_7975143 4095081647339995950035491 := by
  unfold tailWord_7975143
  simp only [CollatzResearch.WordTrace]
  refine ⟨290877361746426431831490083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193918241164284287887660055 290877361746426431831490083)
  ·
    refine ⟨436316042619639647747235125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290877361746426431831490083 436316042619639647747235125)
    ·
      refine ⟨40904628995591216976303293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 436316042619639647747235125 40904628995591216976303293)
      ·
        refine ⟨15339235873346706366113735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40904628995591216976303293 15339235873346706366113735)
        ·
          refine ⟨23008853810020059549170603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15339235873346706366113735 23008853810020059549170603)
          ·
            refine ⟨34513280715030089323755905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23008853810020059549170603 34513280715030089323755905)
            ·
              refine ⟨25884960536272566992816929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34513280715030089323755905 25884960536272566992816929)
              ·
                refine ⟨19413720402204425244612697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25884960536272566992816929 19413720402204425244612697)
                ·
                  refine ⟨14560290301653318933459523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19413720402204425244612697 14560290301653318933459523)
                  ·
                    refine ⟨21840435452479978400189285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14560290301653318933459523 21840435452479978400189285)
                    ·
                      refine ⟨4095081647339995950035491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21840435452479978400189285 4095081647339995950035491)
                      ·
                        rfl

theorem cell23_7975143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_7975143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975143 prefixEnd_7975143 := by exact prefixLift 7975143
  have htrace : WordTrace (prefixWord ++ tailWord_7975143) baseStart_7975143 baseEnd_7975143 := by
    simpa [prefixWord, tailWord_7975143, baseEnd_7975143] using wordTrace_append hprefix tailTrace_7975143
  have hstable : (prefixWord ++ tailWord_7975143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975143).length < 2 ^ (prefixWord ++ tailWord_7975143).sum := by decide
  have hdescent : baseEnd_7975143 < baseStart_7975143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975170 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_7975170 : Nat := 118140960795 + 7975170 * 2 ^ 59
def prefixEnd_7975170 : Nat := 4983230072969 + 3 ^ 40 * 7975170 * 2
def baseEnd_7975170 : Nat := 1365031837105889114799289

theorem tailTrace_7975170 : CollatzResearch.WordTrace tailWord_7975170 prefixEnd_7975170 1365031837105889114799289 := by
  unfold tailWord_7975170
  simp only [CollatzResearch.WordTrace]
  refine ⟨72719586629332153860680741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193918897678219076961815309 72719586629332153860680741)
  ·
    refine ⟨13634922492999778848877639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72719586629332153860680741 13634922492999778848877639)
    ·
      refine ⟨20452383739499668273316459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13634922492999778848877639 20452383739499668273316459)
      ·
        refine ⟨30678575609249502409974689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20452383739499668273316459 30678575609249502409974689)
        ·
          refine ⟨23008931706937126807481017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30678575609249502409974689 23008931706937126807481017)
          ·
            refine ⟨17256698780202845105610763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23008931706937126807481017 17256698780202845105610763)
            ·
              refine ⟨25885048170304267658416145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17256698780202845105610763 25885048170304267658416145)
              ·
                refine ⟨19413786127728200743812109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25885048170304267658416145 19413786127728200743812109)
                ·
                  refine ⟨7280169797898075278929541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19413786127728200743812109 7280169797898075278929541)
                  ·
                    refine ⟨1365031837105889114799289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7280169797898075278929541 1365031837105889114799289)
                    ·
                      rfl

theorem cell23_7975170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_7975170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975170 prefixEnd_7975170 := by exact prefixLift 7975170
  have htrace : WordTrace (prefixWord ++ tailWord_7975170) baseStart_7975170 baseEnd_7975170 := by
    simpa [prefixWord, tailWord_7975170, baseEnd_7975170] using wordTrace_append hprefix tailTrace_7975170
  have hstable : (prefixWord ++ tailWord_7975170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975170).length < 2 ^ (prefixWord ++ tailWord_7975170).sum := by decide
  have hdescent : baseEnd_7975170 < baseStart_7975170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975203 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 4, 3, 2]
def baseStart_7975203 : Nat := 118140960795 + 7975203 * 2 ^ 59
def prefixEnd_7975203 : Nat := 4983230072969 + 3 ^ 40 * 7975203 * 2
def baseEnd_7975203 : Nat := 4095112456179265715285215

theorem tailTrace_7975203 : CollatzResearch.WordTrace tailWord_7975203 prefixEnd_7975203 4095112456179265715285215 := by
  unfold tailWord_7975203
  simp only [CollatzResearch.WordTrace]
  refine ⟨290879550126209062078674263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193919700084139374719116175 290879550126209062078674263)
  ·
    refine ⟨436319325189313593118011395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290879550126209062078674263 436319325189313593118011395)
    ·
      refine ⟨654478987783970389677017093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436319325189313593118011395 654478987783970389677017093)
      ·
        refine ⟨122714810209494448064440705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 654478987783970389677017093 122714810209494448064440705)
        ·
          refine ⟨92036107657120836048330529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122714810209494448064440705 92036107657120836048330529)
          ·
            refine ⟨69027080742840627036247897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92036107657120836048330529 69027080742840627036247897)
            ·
              refine ⟨51770310557130470277185923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69027080742840627036247897 51770310557130470277185923)
              ·
                refine ⟨77655465835695705415778885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51770310557130470277185923 77655465835695705415778885)
                ·
                  refine ⟨14560399844192944765458541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77655465835695705415778885 14560399844192944765458541)
                  ·
                    refine ⟨5460149941572354287046953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14560399844192944765458541 5460149941572354287046953)
                    ·
                      refine ⟨4095112456179265715285215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460149941572354287046953 4095112456179265715285215)
                      ·
                        rfl

theorem cell23_7975203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_7975203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975203 prefixEnd_7975203 := by exact prefixLift 7975203
  have htrace : WordTrace (prefixWord ++ tailWord_7975203) baseStart_7975203 baseEnd_7975203 := by
    simpa [prefixWord, tailWord_7975203, baseEnd_7975203] using wordTrace_append hprefix tailTrace_7975203
  have hstable : (prefixWord ++ tailWord_7975203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975203).length < 2 ^ (prefixWord ++ tailWord_7975203).sum := by decide
  have hdescent : baseEnd_7975203 < baseStart_7975203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975216 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 4]
def baseStart_7975216 : Nat := 118140960795 + 7975216 * 2 ^ 59
def prefixEnd_7975216 : Nat := 4983230072969 + 3 ^ 40 * 7975216 * 2
def baseEnd_7975216 : Nat := 4095119131427774164422655

theorem tailTrace_7975216 : CollatzResearch.WordTrace tailWord_7975216 prefixEnd_7975216 4095119131427774164422655 := by
  unfold tailWord_7975216
  simp only [CollatzResearch.WordTrace]
  refine ⟨145440012137580982649448751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193920016183441310199265001 145440012137580982649448751)
  ·
    refine ⟨218160018206371473974173127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145440012137580982649448751 218160018206371473974173127)
    ·
      refine ⟨327240027309557210961259691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218160018206371473974173127 327240027309557210961259691)
      ·
        refine ⟨490860040964335816441889537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327240027309557210961259691 490860040964335816441889537)
        ·
          refine ⟨368145030723251862331417153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490860040964335816441889537 368145030723251862331417153)
          ·
            refine ⟨276108773042438896748562865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368145030723251862331417153 276108773042438896748562865)
            ·
              refine ⟨207081579781829172561422149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276108773042438896748562865 207081579781829172561422149)
              ·
                refine ⟨38827796209092969855266653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207081579781829172561422149 38827796209092969855266653)
                ·
                  refine ⟨14560423578409863695724995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38827796209092969855266653 14560423578409863695724995)
                  ·
                    refine ⟨21840635367614795543587493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14560423578409863695724995 21840635367614795543587493)
                    ·
                      refine ⟨4095119131427774164422655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21840635367614795543587493 4095119131427774164422655)
                      ·
                        rfl

theorem cell23_7975216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_7975216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975216 prefixEnd_7975216 := by exact prefixLift 7975216
  have htrace : WordTrace (prefixWord ++ tailWord_7975216) baseStart_7975216 baseEnd_7975216 := by
    simpa [prefixWord, tailWord_7975216, baseEnd_7975216] using wordTrace_append hprefix tailTrace_7975216
  have hstable : (prefixWord ++ tailWord_7975216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975216).length < 2 ^ (prefixWord ++ tailWord_7975216).sum := by decide
  have hdescent : baseEnd_7975216 < baseStart_7975216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975220 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_7975220 : Nat := 118140960795 + 7975220 * 2 ^ 59
def prefixEnd_7975220 : Nat := 4983230072969 + 3 ^ 40 * 7975220 * 2
def baseEnd_7975220 : Nat := 4095121185350392148772637

theorem tailTrace_7975220 : CollatzResearch.WordTrace tailWord_7975220 prefixEnd_7975220 4095121185350392148772637 := by
  unfold tailWord_7975220
  simp only [CollatzResearch.WordTrace]
  refine ⟨145440085083573736991021557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193920113444764982654695409 145440085083573736991021557)
  ·
    refine ⟨13635007976585037842908271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145440085083573736991021557 13635007976585037842908271)
    ·
      refine ⟨20452511964877556764362407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13635007976585037842908271 20452511964877556764362407)
      ·
        refine ⟨30678767947316335146543611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20452511964877556764362407 30678767947316335146543611)
        ·
          refine ⟨46018151920974502719815417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30678767947316335146543611 46018151920974502719815417)
          ·
            refine ⟨34513613940730877039861563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46018151920974502719815417 34513613940730877039861563)
            ·
              refine ⟨51770420911096315559792345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34513613940730877039861563 51770420911096315559792345)
              ·
                refine ⟨38827815683322236669844259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51770420911096315559792345 38827815683322236669844259)
                ·
                  refine ⟨58241723524983355004766389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38827815683322236669844259 58241723524983355004766389)
                  ·
                    refine ⟨5460161580467189531696849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58241723524983355004766389 5460161580467189531696849)
                    ·
                      refine ⟨4095121185350392148772637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460161580467189531696849 4095121185350392148772637)
                      ·
                        rfl

theorem cell23_7975220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_7975220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975220 prefixEnd_7975220 := by exact prefixLift 7975220
  have htrace : WordTrace (prefixWord ++ tailWord_7975220) baseStart_7975220 baseEnd_7975220 := by
    simpa [prefixWord, tailWord_7975220, baseEnd_7975220] using wordTrace_append hprefix tailTrace_7975220
  have hstable : (prefixWord ++ tailWord_7975220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975220).length < 2 ^ (prefixWord ++ tailWord_7975220).sum := by decide
  have hdescent : baseEnd_7975220 < baseStart_7975220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975230 : List Nat := [4, 2, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_7975230 : Nat := 118140960795 + 7975230 * 2 ^ 59
def prefixEnd_7975230 : Nat := 4983230072969 + 3 ^ 40 * 7975230 * 2
def baseEnd_7975230 : Nat := 1365042106718979036549197

theorem tailTrace_7975230 : CollatzResearch.WordTrace tailWord_7975230 prefixEnd_7975230 1365042106718979036549197 := by
  unfold tailWord_7975230
  simp only [CollatzResearch.WordTrace]
  refine ⟨36360066862138905711238393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193920356598074163793271429 36360066862138905711238393)
  ·
    refine ⟨27270050146604179283428795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36360066862138905711238393 27270050146604179283428795)
    ·
      refine ⟨40905075219906268925143193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27270050146604179283428795 40905075219906268925143193)
      ·
        refine ⟨30678806414929701693857395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40905075219906268925143193 30678806414929701693857395)
        ·
          refine ⟨46018209622394552540786093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30678806414929701693857395 46018209622394552540786093)
          ·
            refine ⟨17256828608397957202794785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46018209622394552540786093 17256828608397957202794785)
            ·
              refine ⟨12942621456298467902096089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17256828608397957202794785 12942621456298467902096089)
              ·
                refine ⟨9706966092223850926572067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12942621456298467902096089 9706966092223850926572067)
                ·
                  refine ⟨14560449138335776389858101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9706966092223850926572067 14560449138335776389858101)
                  ·
                    refine ⟨1365042106718979036549197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14560449138335776389858101 1365042106718979036549197)
                    ·
                      rfl

theorem cell23_7975230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_7975230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975230 prefixEnd_7975230 := by exact prefixLift 7975230
  have htrace : WordTrace (prefixWord ++ tailWord_7975230) baseStart_7975230 baseEnd_7975230 := by
    simpa [prefixWord, tailWord_7975230, baseEnd_7975230] using wordTrace_append hprefix tailTrace_7975230
  have hstable : (prefixWord ++ tailWord_7975230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975230).length < 2 ^ (prefixWord ++ tailWord_7975230).sum := by decide
  have hdescent : baseEnd_7975230 < baseStart_7975230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975250 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_7975250 : Nat := 118140960795 + 7975250 * 2 ^ 59
def prefixEnd_7975250 : Nat := 4983230072969 + 3 ^ 40 * 7975250 * 2
def baseEnd_7975250 : Nat := 4095136589770027031397499

theorem tailTrace_7975250 : CollatzResearch.WordTrace tailWord_7975250 prefixEnd_7975250 4095136589770027031397499 := by
  unfold tailWord_7975250
  simp only [CollatzResearch.WordTrace]
  refine ⟨72720316089259697276408801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193920842904692526070423469 72720316089259697276408801)
  ·
    refine ⟨54540237066944772957306601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72720316089259697276408801 54540237066944772957306601)
    ·
      refine ⟨40905177800208579717979951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54540237066944772957306601 40905177800208579717979951)
      ·
        refine ⟨61357766700312869576969927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40905177800208579717979951 61357766700312869576969927)
        ·
          refine ⟨92036650050469304365454891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61357766700312869576969927 92036650050469304365454891)
          ·
            refine ⟨138054975075703956548182337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92036650050469304365454891 138054975075703956548182337)
            ·
              refine ⟨103541231306777967411136753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138054975075703956548182337 103541231306777967411136753)
              ·
                refine ⟨77655923480083475558352565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103541231306777967411136753 77655923480083475558352565)
                ·
                  refine ⟨7280242826257825833595553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77655923480083475558352565 7280242826257825833595553)
                  ·
                    refine ⟨5460182119693369375196665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7280242826257825833595553 5460182119693369375196665)
                    ·
                      refine ⟨4095136589770027031397499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460182119693369375196665 4095136589770027031397499)
                      ·
                        rfl

theorem cell23_7975250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_7975250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975250 prefixEnd_7975250 := by exact prefixLift 7975250
  have htrace : WordTrace (prefixWord ++ tailWord_7975250) baseStart_7975250 baseEnd_7975250 := by
    simpa [prefixWord, tailWord_7975250, baseEnd_7975250] using wordTrace_append hprefix tailTrace_7975250
  have hstable : (prefixWord ++ tailWord_7975250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975250).length < 2 ^ (prefixWord ++ tailWord_7975250).sum := by decide
  have hdescent : baseEnd_7975250 < baseStart_7975250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975340 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 6, 2, 2]
def baseStart_7975340 : Nat := 118140960795 + 7975340 * 2 ^ 59
def prefixEnd_7975340 : Nat := 4983230072969 + 3 ^ 40 * 7975340 * 2
def baseEnd_7975340 : Nat := 4095182803028931679272085

theorem tailTrace_7975340 : CollatzResearch.WordTrace tailWord_7975340 prefixEnd_7975340 4095182803028931679272085 := by
  unfold tailWord_7975340
  simp only [CollatzResearch.WordTrace]
  refine ⟨145442273463356367238205737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193923031284475156317607649 145442273463356367238205737)
  ·
    refine ⟨109081705097517275428654303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145442273463356367238205737 109081705097517275428654303)
    ·
      refine ⟨163622557646275913142981455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109081705097517275428654303 163622557646275913142981455)
      ·
        refine ⟨245433836469413869714472183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163622557646275913142981455 245433836469413869714472183)
        ·
          refine ⟨368150754704120804571708275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245433836469413869714472183 368150754704120804571708275)
          ·
            refine ⟨552226132056181206857562413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368150754704120804571708275 552226132056181206857562413)
            ·
              refine ⟨207084799521067952571585905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 552226132056181206857562413 207084799521067952571585905)
              ·
                refine ⟨155313599640800964428689429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207084799521067952571585905 155313599640800964428689429)
                ·
                  refine ⟨7280324983162545207594817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155313599640800964428689429 7280324983162545207594817)
                  ·
                    refine ⟨5460243737371908905696113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7280324983162545207594817 5460243737371908905696113)
                    ·
                      refine ⟨4095182803028931679272085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460243737371908905696113 4095182803028931679272085)
                      ·
                        rfl

theorem cell23_7975340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 2, 2].length) (baseStart_7975340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975340 prefixEnd_7975340 := by exact prefixLift 7975340
  have htrace : WordTrace (prefixWord ++ tailWord_7975340) baseStart_7975340 baseEnd_7975340 := by
    simpa [prefixWord, tailWord_7975340, baseEnd_7975340] using wordTrace_append hprefix tailTrace_7975340
  have hstable : (prefixWord ++ tailWord_7975340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975340).length < 2 ^ (prefixWord ++ tailWord_7975340).sum := by decide
  have hdescent : baseEnd_7975340 < baseStart_7975340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975376 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 5, 7]
def baseStart_7975376 : Nat := 118140960795 + 7975376 * 2 ^ 59
def prefixEnd_7975376 : Nat := 4983230072969 + 3 ^ 40 * 7975376 * 2
def baseEnd_7975376 : Nat := 1365067096110831179473973

theorem tailTrace_7975376 : CollatzResearch.WordTrace tailWord_7975376 prefixEnd_7975376 1365067096110831179473973 := by
  unfold tailWord_7975376
  simp only [CollatzResearch.WordTrace]
  refine ⟨145442929977291156312360991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193923906636388208416481321 145442929977291156312360991)
  ·
    refine ⟨218164394965936734468541487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145442929977291156312360991 218164394965936734468541487)
    ·
      refine ⟨327246592448905101702812231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218164394965936734468541487 327246592448905101702812231)
      ·
        refine ⟨490869888673357652554218347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327246592448905101702812231 490869888673357652554218347)
        ·
          refine ⟨736304833010036478831327521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490869888673357652554218347 736304833010036478831327521)
          ·
            refine ⟨552228624757527359123495641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736304833010036478831327521 552228624757527359123495641)
            ·
              refine ⟨414171468568145519342621731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552228624757527359123495641 414171468568145519342621731)
              ·
                refine ⟨621257202852218279013932597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414171468568145519342621731 621257202852218279013932597)
                ·
                  refine ⟨58242862767395463657556181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 621257202852218279013932597 58242862767395463657556181)
                  ·
                    refine ⟨1365067096110831179473973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58242862767395463657556181 1365067096110831179473973)
                    ·
                      rfl

theorem cell23_7975376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_7975376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975376 prefixEnd_7975376 := by exact prefixLift 7975376
  have htrace : WordTrace (prefixWord ++ tailWord_7975376) baseStart_7975376 baseEnd_7975376 := by
    simpa [prefixWord, tailWord_7975376, baseEnd_7975376] using wordTrace_append hprefix tailTrace_7975376
  have hstable : (prefixWord ++ tailWord_7975376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975376).length < 2 ^ (prefixWord ++ tailWord_7975376).sum := by decide
  have hdescent : baseEnd_7975376 < baseStart_7975376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975380 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 7]
def baseStart_7975380 : Nat := 118140960795 + 7975380 * 2 ^ 59
def prefixEnd_7975380 : Nat := 4983230072969 + 3 ^ 40 * 7975380 * 2
def baseEnd_7975380 : Nat := 455022593583901280307989

theorem tailTrace_7975380 : CollatzResearch.WordTrace tailWord_7975380 prefixEnd_7975380 455022593583901280307989 := by
  unfold tailWord_7975380
  simp only [CollatzResearch.WordTrace]
  refine ⟨145443002923283910653933797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193924003897711880871911729 145443002923283910653933797)
  ·
    refine ⟨27270563048115733247612587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145443002923283910653933797 27270563048115733247612587)
    ·
      refine ⟨40905844572173599871418881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27270563048115733247612587 40905844572173599871418881)
      ·
        refine ⟨30679383429130199903564161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40905844572173599871418881 30679383429130199903564161)
        ·
          refine ⟨23009537571847649927673121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30679383429130199903564161 23009537571847649927673121)
          ·
            refine ⟨17257153178885737445754841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23009537571847649927673121 17257153178885737445754841)
            ·
              refine ⟨12942864884164303084316131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17257153178885737445754841 12942864884164303084316131)
              ·
                refine ⟨19414297326246454626474197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12942864884164303084316131 19414297326246454626474197)
                ·
                  refine ⟨455022593583901280307989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19414297326246454626474197 455022593583901280307989)
                  ·
                    rfl

theorem cell23_7975380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_7975380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975380 prefixEnd_7975380 := by exact prefixLift 7975380
  have htrace : WordTrace (prefixWord ++ tailWord_7975380) baseStart_7975380 baseEnd_7975380 := by
    simpa [prefixWord, tailWord_7975380, baseEnd_7975380] using wordTrace_append hprefix tailTrace_7975380
  have hstable : (prefixWord ++ tailWord_7975380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975380).length < 2 ^ (prefixWord ++ tailWord_7975380).sum := by decide
  have hdescent : baseEnd_7975380 < baseStart_7975380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975433 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 3, 4, 3]
def baseStart_7975433 : Nat := 118140960795 + 7975433 * 2 ^ 59
def prefixEnd_7975433 : Nat := 4983230072969 + 3 ^ 40 * 7975433 * 2
def baseEnd_7975433 : Nat := 4095230556729799815409157

theorem tailTrace_7975433 : CollatzResearch.WordTrace tailWord_7975433 prefixEnd_7975433 4095230556729799815409157 := by
  unfold tailWord_7975433
  simp only [CollatzResearch.WordTrace]
  refine ⟨290887938915375811359546953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193925292610250540906364635 290887938915375811359546953)
  ·
    refine ⟨218165954186531858519660215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290887938915375811359546953 218165954186531858519660215)
    ·
      refine ⟨327248931279797787779490323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218165954186531858519660215 327248931279797787779490323)
      ·
        refine ⟨490873396919696681669235485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327248931279797787779490323 490873396919696681669235485)
        ·
          refine ⟨184077523844886255625963307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490873396919696681669235485 184077523844886255625963307)
          ·
            refine ⟨276116285767329383438944961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184077523844886255625963307 276116285767329383438944961)
            ·
              refine ⟨207087214325497037579208721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276116285767329383438944961 207087214325497037579208721)
              ·
                refine ⟨155315410744122778184406541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207087214325497037579208721 155315410744122778184406541)
                ·
                  refine ⟨58243279029046041819152453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155315410744122778184406541 58243279029046041819152453)
                  ·
                    refine ⟨10920614817946132841091085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58243279029046041819152453 10920614817946132841091085)
                    ·
                      refine ⟨4095230556729799815409157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10920614817946132841091085 4095230556729799815409157)
                      ·
                        rfl

theorem cell23_7975433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 4, 3].length) (baseStart_7975433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975433 prefixEnd_7975433 := by exact prefixLift 7975433
  have htrace : WordTrace (prefixWord ++ tailWord_7975433) baseStart_7975433 baseEnd_7975433 := by
    simpa [prefixWord, tailWord_7975433, baseEnd_7975433] using wordTrace_append hprefix tailTrace_7975433
  have hstable : (prefixWord ++ tailWord_7975433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975433).length < 2 ^ (prefixWord ++ tailWord_7975433).sum := by decide
  have hdescent : baseEnd_7975433 < baseStart_7975433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975437 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_7975437 : Nat := 118140960795 + 7975437 * 2 ^ 59
def prefixEnd_7975437 : Nat := 4983230072969 + 3 ^ 40 * 7975437 * 2
def baseEnd_7975437 : Nat := 4095232610652417799759139

theorem tailTrace_7975437 : CollatzResearch.WordTrace tailWord_7975437 prefixEnd_7975437 4095232610652417799759139 := by
  unfold tailWord_7975437
  simp only [CollatzResearch.WordTrace]
  refine ⟨290888084807361320042692565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193925389871574213361795043 290888084807361320042692565)
  ·
    refine ⟨6817689487672530938500607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 290888084807361320042692565 6817689487672530938500607)
    ·
      refine ⟨10226534231508796407750911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6817689487672530938500607 10226534231508796407750911)
      ·
        refine ⟨15339801347263194611626367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10226534231508796407750911 15339801347263194611626367)
        ·
          refine ⟨23009702020894791917439551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15339801347263194611626367 23009702020894791917439551)
          ·
            refine ⟨34514553031342187876159327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23009702020894791917439551 34514553031342187876159327)
            ·
              refine ⟨51771829547013281814238991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34514553031342187876159327 51771829547013281814238991)
              ·
                refine ⟨77657744320519922721358487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51771829547013281814238991 77657744320519922721358487)
                ·
                  refine ⟨116486616480779884082037731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77657744320519922721358487 116486616480779884082037731)
                  ·
                    refine ⟨174729924721169826123056597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116486616480779884082037731 174729924721169826123056597)
                    ·
                      refine ⟨4095232610652417799759139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174729924721169826123056597 4095232610652417799759139)
                      ·
                        rfl

theorem cell23_7975437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_7975437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975437 prefixEnd_7975437 := by exact prefixLift 7975437
  have htrace : WordTrace (prefixWord ++ tailWord_7975437) baseStart_7975437 baseEnd_7975437 := by
    simpa [prefixWord, tailWord_7975437, baseEnd_7975437] using wordTrace_append hprefix tailTrace_7975437
  have hstable : (prefixWord ++ tailWord_7975437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975437).length < 2 ^ (prefixWord ++ tailWord_7975437).sum := by decide
  have hdescent : baseEnd_7975437 < baseStart_7975437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975520 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 4]
def baseStart_7975520 : Nat := 118140960795 + 7975520 * 2 ^ 59
def prefixEnd_7975520 : Nat := 4983230072969 + 3 ^ 40 * 7975520 * 2
def baseEnd_7975520 : Nat := 4095275229546740975021257

theorem tailTrace_7975520 : CollatzResearch.WordTrace tailWord_7975520 prefixEnd_7975520 4095275229546740975021257 := by
  unfold tailWord_7975520
  simp only [CollatzResearch.WordTrace]
  refine ⟨145445556033030312608982007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193927408044040416811976009 145445556033030312608982007)
  ·
    refine ⟨218168334049545468913473011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145445556033030312608982007 218168334049545468913473011)
    ·
      refine ⟨327252501074318203370209517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218168334049545468913473011 327252501074318203370209517)
      ·
        refine ⟨122719687902869326263828569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327252501074318203370209517 122719687902869326263828569)
        ·
          refine ⟨92039765927151994697871427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122719687902869326263828569 92039765927151994697871427)
          ·
            refine ⟨138059648890727992046807141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92039765927151994697871427 138059648890727992046807141)
            ·
              refine ⟨25886184167011498508776339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138059648890727992046807141 25886184167011498508776339)
              ·
                refine ⟨38829276250517247763164509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25886184167011498508776339 38829276250517247763164509)
                ·
                  refine ⟨14560978593943967911186691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38829276250517247763164509 14560978593943967911186691)
                  ·
                    refine ⟨21841467890915951866780037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14560978593943967911186691 21841467890915951866780037)
                    ·
                      refine ⟨4095275229546740975021257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21841467890915951866780037 4095275229546740975021257)
                      ·
                        rfl

theorem cell23_7975520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_7975520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975520 prefixEnd_7975520 := by exact prefixLift 7975520
  have htrace : WordTrace (prefixWord ++ tailWord_7975520) baseStart_7975520 baseEnd_7975520 := by
    simpa [prefixWord, tailWord_7975520, baseEnd_7975520] using wordTrace_append hprefix tailTrace_7975520
  have hstable : (prefixWord ++ tailWord_7975520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975520).length < 2 ^ (prefixWord ++ tailWord_7975520).sum := by decide
  have hdescent : baseEnd_7975520 < baseStart_7975520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975530 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 1, 6]
def baseStart_7975530 : Nat := 118140960795 + 7975530 * 2 ^ 59
def prefixEnd_7975530 : Nat := 4983230072969 + 3 ^ 40 * 7975530 * 2
def baseEnd_7975530 : Nat := 1365093454784428645298737

theorem tailTrace_7975530 : CollatzResearch.WordTrace tailWord_7975530 prefixEnd_7975530 1365093454784428645298737 := by
  unfold tailWord_7975530
  simp only [CollatzResearch.WordTrace]
  refine ⟨72722869199006099231457011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193927651197349597950552029 72722869199006099231457011)
  ·
    refine ⟨109084303798509148847185517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72722869199006099231457011 109084303798509148847185517)
    ·
      refine ⟨40906613924440930817694569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109084303798509148847185517 40906613924440930817694569)
      ·
        refine ⟨30679960443330698113270927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40906613924440930817694569 30679960443330698113270927)
        ·
          refine ⟨46019940664996047169906391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30679960443330698113270927 46019940664996047169906391)
          ·
            refine ⟨69029910997494070754859587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46019940664996047169906391 69029910997494070754859587)
            ·
              refine ⟨103544866496241106132289381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69029910997494070754859587 103544866496241106132289381)
              ·
                refine ⟨19414662468045207399804259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103544866496241106132289381 19414662468045207399804259)
                ·
                  refine ⟨29121993702067811099706389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19414662468045207399804259 29121993702067811099706389)
                  ·
                    refine ⟨1365093454784428645298737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29121993702067811099706389 1365093454784428645298737)
                    ·
                      rfl

theorem cell23_7975530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_7975530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975530 prefixEnd_7975530 := by exact prefixLift 7975530
  have htrace : WordTrace (prefixWord ++ tailWord_7975530) baseStart_7975530 baseEnd_7975530 := by
    simpa [prefixWord, tailWord_7975530, baseEnd_7975530] using wordTrace_append hprefix tailTrace_7975530
  have hstable : (prefixWord ++ tailWord_7975530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975530).length < 2 ^ (prefixWord ++ tailWord_7975530).sum := by decide
  have hdescent : baseEnd_7975530 < baseStart_7975530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975534 : List Nat := [4, 1, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_7975534 : Nat := 118140960795 + 7975534 * 2 ^ 59
def prefixEnd_7975534 : Nat := 4983230072969 + 3 ^ 40 * 7975534 * 2
def baseEnd_7975534 : Nat := 1365094139425301306748731

theorem tailTrace_7975534 : CollatzResearch.WordTrace tailWord_7975534 prefixEnd_7975534 1365094139425301306748731 := by
  unfold tailWord_7975534
  simp only [CollatzResearch.WordTrace]
  refine ⟨36361452836001238201121707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193927748458673270405982437 36361452836001238201121707)
  ·
    refine ⟨54542179254001857301682561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36361452836001238201121707 54542179254001857301682561)
    ·
      refine ⟨40906634440501392976261921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54542179254001857301682561 40906634440501392976261921)
      ·
        refine ⟨30679975830376044732196441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40906634440501392976261921 30679975830376044732196441)
        ·
          refine ⟨23009981872782033549147331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30679975830376044732196441 23009981872782033549147331)
          ·
            refine ⟨34514972809173050323720997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23009981872782033549147331 34514972809173050323720997)
            ·
              refine ⟨6471557401719946935697687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34514972809173050323720997 6471557401719946935697687)
              ·
                refine ⟨9707336102579920403546531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6471557401719946935697687 9707336102579920403546531)
                ·
                  refine ⟨14561004153869880605319797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9707336102579920403546531 14561004153869880605319797)
                  ·
                    refine ⟨1365094139425301306748731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14561004153869880605319797 1365094139425301306748731)
                    ·
                      rfl

theorem cell23_7975534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_7975534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975534 prefixEnd_7975534 := by exact prefixLift 7975534
  have htrace : WordTrace (prefixWord ++ tailWord_7975534) baseStart_7975534 baseEnd_7975534 := by
    simpa [prefixWord, tailWord_7975534, baseEnd_7975534] using wordTrace_append hprefix tailTrace_7975534
  have hstable : (prefixWord ++ tailWord_7975534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975534).length < 2 ^ (prefixWord ++ tailWord_7975534).sum := by decide
  have hdescent : baseEnd_7975534 < baseStart_7975534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975563 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 6]
def baseStart_7975563 : Nat := 118140960795 + 7975563 * 2 ^ 59
def prefixEnd_7975563 : Nat := 4983230072969 + 3 ^ 40 * 7975563 * 2
def baseEnd_7975563 : Nat := 4095297309214884306783559

theorem tailTrace_7975563 : CollatzResearch.WordTrace tailWord_7975563 prefixEnd_7975563 4095297309214884306783559 := by
  unfold tailWord_7975563
  simp only [CollatzResearch.WordTrace]
  refine ⟨290892680404904843561779343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193928453603269895707852895 290892680404904843561779343)
  ·
    refine ⟨436339020607357265342669015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290892680404904843561779343 436339020607357265342669015)
    ·
      refine ⟨654508530911035898014003523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436339020607357265342669015 654508530911035898014003523)
      ·
        refine ⟨981762796366553847021005285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654508530911035898014003523 981762796366553847021005285)
        ·
          refine ⟨184080524318728846316438491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 981762796366553847021005285 184080524318728846316438491)
          ·
            refine ⟨276120786478093269474657737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184080524318728846316438491 276120786478093269474657737)
            ·
              refine ⟨207090589858569952105993303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276120786478093269474657737 207090589858569952105993303)
              ·
                refine ⟨310635884787854928158989955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207090589858569952105993303 310635884787854928158989955)
                ·
                  refine ⟨465953827181782392238484933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310635884787854928158989955 465953827181782392238484933)
                  ·
                    refine ⟨87366342596584198544715925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 465953827181782392238484933 87366342596584198544715925)
                    ·
                      refine ⟨4095297309214884306783559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87366342596584198544715925 4095297309214884306783559)
                      ·
                        rfl

theorem cell23_7975563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_7975563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975563 prefixEnd_7975563 := by exact prefixLift 7975563
  have htrace : WordTrace (prefixWord ++ tailWord_7975563) baseStart_7975563 baseEnd_7975563 := by
    simpa [prefixWord, tailWord_7975563, baseEnd_7975563] using wordTrace_append hprefix tailTrace_7975563
  have hstable : (prefixWord ++ tailWord_7975563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975563).length < 2 ^ (prefixWord ++ tailWord_7975563).sum := by decide
  have hdescent : baseEnd_7975563 < baseStart_7975563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975594 : List Nat := [3, 1, 5, 2, 1, 2, 9]
def baseStart_7975594 : Nat := 118140960795 + 7975594 * 2 ^ 59
def prefixEnd_7975594 : Nat := 4983230072969 + 3 ^ 40 * 7975594 * 2
def baseEnd_7975594 : Nat := 50559422556977452907357

theorem tailTrace_7975594 : CollatzResearch.WordTrace tailWord_7975594 prefixEnd_7975594 50559422556977452907357 := by
  unfold tailWord_7975594
  simp only [CollatzResearch.WordTrace]
  refine ⟨72723452766948133964039459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193929207378528357237438557 72723452766948133964039459)
  ·
    refine ⟨109085179150422200946059189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72723452766948133964039459 109085179150422200946059189)
    ·
      refine ⟨10226735545352081338693049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109085179150422200946059189 10226735545352081338693049)
      ·
        refine ⟨7670051659014061004019787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10226735545352081338693049 7670051659014061004019787)
        ·
          refine ⟨11505077488521091506029681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7670051659014061004019787 11505077488521091506029681)
          ·
            refine ⟨8628808116390818629522261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11505077488521091506029681 8628808116390818629522261)
            ·
              refine ⟨50559422556977452907357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8628808116390818629522261 50559422556977452907357)
              ·
                rfl

theorem cell23_7975594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 9].length) (baseStart_7975594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975594 prefixEnd_7975594 := by exact prefixLift 7975594
  have htrace : WordTrace (prefixWord ++ tailWord_7975594) baseStart_7975594 baseEnd_7975594 := by
    simpa [prefixWord, tailWord_7975594, baseEnd_7975594] using wordTrace_append hprefix tailTrace_7975594
  have hstable : (prefixWord ++ tailWord_7975594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975594).length < 2 ^ (prefixWord ++ tailWord_7975594).sum := by decide
  have hdescent : baseEnd_7975594 < baseStart_7975594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975605 : List Nat := [1, 3, 3, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_7975605 : Nat := 118140960795 + 7975605 * 2 ^ 59
def prefixEnd_7975605 : Nat := 4983230072969 + 3 ^ 40 * 7975605 * 2
def baseEnd_7975605 : Nat := 4095318875402373142458367

theorem tailTrace_7975605 : CollatzResearch.WordTrace tailWord_7975605 prefixEnd_7975605 4095318875402373142458367 := by
  unfold tailWord_7975605
  simp only [CollatzResearch.WordTrace]
  refine ⟨290894212270752684734808269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193929474847168456489872179 290894212270752684734808269)
  ·
    refine ⟨109085329601532256775553101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290894212270752684734808269 109085329601532256775553101)
    ·
      refine ⟨40906998600574596290832413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109085329601532256775553101 40906998600574596290832413)
      ·
        refine ⟨15340124475215473609062155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40906998600574596290832413 15340124475215473609062155)
        ·
          refine ⟨23010186712823210413593233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15340124475215473609062155 23010186712823210413593233)
          ·
            refine ⟨17257640034617407810194925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23010186712823210413593233 17257640034617407810194925)
            ·
              refine ⟨6471615012981527928823097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17257640034617407810194925 6471615012981527928823097)
              ·
                refine ⟨4853711259736145946617323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6471615012981527928823097 4853711259736145946617323)
                ·
                  refine ⟨7280566889604218919925985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4853711259736145946617323 7280566889604218919925985)
                  ·
                    refine ⟨5460425167203164189944489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7280566889604218919925985 5460425167203164189944489)
                    ·
                      refine ⟨4095318875402373142458367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460425167203164189944489 4095318875402373142458367)
                      ·
                        rfl

theorem cell23_7975605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_7975605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975605 prefixEnd_7975605 := by exact prefixLift 7975605
  have htrace : WordTrace (prefixWord ++ tailWord_7975605) baseStart_7975605 baseEnd_7975605 := by
    simpa [prefixWord, tailWord_7975605, baseEnd_7975605] using wordTrace_append hprefix tailTrace_7975605
  have hstable : (prefixWord ++ tailWord_7975605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975605).length < 2 ^ (prefixWord ++ tailWord_7975605).sum := by decide
  have hdescent : baseEnd_7975605 < baseStart_7975605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975610 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_7975610 : Nat := 118140960795 + 7975610 * 2 ^ 59
def prefixEnd_7975610 : Nat := 4983230072969 + 3 ^ 40 * 7975610 * 2
def baseEnd_7975610 : Nat := 4095321442805645622895843

theorem tailTrace_7975610 : CollatzResearch.WordTrace tailWord_7975610 prefixEnd_7975610 4095321442805645622895843 := by
  unfold tailWord_7975610
  simp only [CollatzResearch.WordTrace]
  refine ⟨72723598658933642647185071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193929596423823047059160189 72723598658933642647185071)
  ·
    refine ⟨109085397988400463970777607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72723598658933642647185071 109085397988400463970777607)
    ·
      refine ⟨163628096982600695956166411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109085397988400463970777607 163628096982600695956166411)
      ·
        refine ⟨245442145473901043934249617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163628096982600695956166411 245442145473901043934249617)
        ·
          refine ⟨184081609105425782950687213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245442145473901043934249617 184081609105425782950687213)
          ·
            refine ⟨69030603414534668606507705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184081609105425782950687213 69030603414534668606507705)
            ·
              refine ⟨51772952560901001454880779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69030603414534668606507705 51772952560901001454880779)
              ·
                refine ⟨77659428841351502182321169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51772952560901001454880779 77659428841351502182321169)
                ·
                  refine ⟨58244571631013626636740877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77659428841351502182321169 58244571631013626636740877)
                  ·
                    refine ⟨21841714361630109988777829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58244571631013626636740877 21841714361630109988777829)
                    ·
                      refine ⟨4095321442805645622895843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21841714361630109988777829 4095321442805645622895843)
                      ·
                        rfl

theorem cell23_7975610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_7975610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975610 prefixEnd_7975610 := by exact prefixLift 7975610
  have htrace : WordTrace (prefixWord ++ tailWord_7975610) baseStart_7975610 baseEnd_7975610 := by
    simpa [prefixWord, tailWord_7975610, baseEnd_7975610] using wordTrace_append hprefix tailTrace_7975610
  have hstable : (prefixWord ++ tailWord_7975610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975610).length < 2 ^ (prefixWord ++ tailWord_7975610).sum := by decide
  have hdescent : baseEnd_7975610 < baseStart_7975610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975614 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_7975614 : Nat := 118140960795 + 7975614 * 2 ^ 59
def prefixEnd_7975614 : Nat := 4983230072969 + 3 ^ 40 * 7975614 * 2
def baseEnd_7975614 : Nat := 4095323496728263607245825

theorem tailTrace_7975614 : CollatzResearch.WordTrace tailWord_7975614 prefixEnd_7975614 4095323496728263607245825 := by
  unfold tailWord_7975614
  simp only [CollatzResearch.WordTrace]
  refine ⟨36361817565965009908985737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193929693685146719514590597 36361817565965009908985737)
  ·
    refine ⟨27271363174473757431739303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36361817565965009908985737 27271363174473757431739303)
    ·
      refine ⟨40907044761710636147608955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27271363174473757431739303 40907044761710636147608955)
      ·
        refine ⟨61360567142565954221413433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40907044761710636147608955 61360567142565954221413433)
        ·
          refine ⟨46020425356924465666060075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61360567142565954221413433 46020425356924465666060075)
          ·
            refine ⟨69030638035386698499090113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46020425356924465666060075 69030638035386698499090113)
            ·
              refine ⟨51772978526540023874317585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69030638035386698499090113 51772978526540023874317585)
              ·
                refine ⟨38829733894905017905738189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51772978526540023874317585 38829733894905017905738189)
                ·
                  refine ⟨14561150210589381714651821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38829733894905017905738189 14561150210589381714651821)
                  ·
                    refine ⟨5460431328971018142994433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14561150210589381714651821 5460431328971018142994433)
                    ·
                      refine ⟨4095323496728263607245825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460431328971018142994433 4095323496728263607245825)
                      ·
                        rfl

theorem cell23_7975614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_7975614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975614 prefixEnd_7975614 := by exact prefixLift 7975614
  have htrace : WordTrace (prefixWord ++ tailWord_7975614) baseStart_7975614 baseEnd_7975614 := by
    simpa [prefixWord, tailWord_7975614, baseEnd_7975614] using wordTrace_append hprefix tailTrace_7975614
  have hstable : (prefixWord ++ tailWord_7975614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975614).length < 2 ^ (prefixWord ++ tailWord_7975614).sum := by decide
  have hdescent : baseEnd_7975614 < baseStart_7975614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975677 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_7975677 : Nat := 118140960795 + 7975677 * 2 ^ 59
def prefixEnd_7975677 : Nat := 4983230072969 + 3 ^ 40 * 7975677 * 2
def baseEnd_7975677 : Nat := 4095355846009496860758035

theorem tailTrace_7975677 : CollatzResearch.WordTrace tailWord_7975677 prefixEnd_7975677 4095355846009496860758035 := by
  unfold tailWord_7975677
  simp only [CollatzResearch.WordTrace]
  refine ⟨290896838326491841031429285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193931225550994560687619523 290896838326491841031429285)
  ·
    refine ⟨54543157186217220193392991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290896838326491841031429285 54543157186217220193392991)
    ·
      refine ⟨81814735779325830290089487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54543157186217220193392991 81814735779325830290089487)
      ·
        refine ⟨122722103668988745435134231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81814735779325830290089487 122722103668988745435134231)
        ·
          refine ⟨184083155503483118152701347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122722103668988745435134231 184083155503483118152701347)
          ·
            refine ⟨276124733255224677229052021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184083155503483118152701347 276124733255224677229052021)
            ·
              refine ⟨25886693742677313490223627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276124733255224677229052021 25886693742677313490223627)
              ·
                refine ⟨38830040614015970235335441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25886693742677313490223627 38830040614015970235335441)
                ·
                  refine ⟨29122530460511977676501581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38830040614015970235335441 29122530460511977676501581)
                  ·
                    refine ⟨10920948922691991628688093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29122530460511977676501581 10920948922691991628688093)
                    ·
                      refine ⟨4095355846009496860758035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10920948922691991628688093 4095355846009496860758035)
                      ·
                        rfl

theorem cell23_7975677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_7975677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975677 prefixEnd_7975677 := by exact prefixLift 7975677
  have htrace : WordTrace (prefixWord ++ tailWord_7975677) baseStart_7975677 baseEnd_7975677 := by
    simpa [prefixWord, tailWord_7975677, baseEnd_7975677] using wordTrace_append hprefix tailTrace_7975677
  have hstable : (prefixWord ++ tailWord_7975677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975677).length < 2 ^ (prefixWord ++ tailWord_7975677).sum := by decide
  have hdescent : baseEnd_7975677 < baseStart_7975677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975678 : List Nat := [4, 2, 2, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_7975678 : Nat := 118140960795 + 7975678 * 2 ^ 59
def prefixEnd_7975678 : Nat := 4983230072969 + 3 ^ 40 * 7975678 * 2
def baseEnd_7975678 : Nat := 4095356359490151356845531

theorem tailTrace_7975678 : CollatzResearch.WordTrace tailWord_7975678 prefixEnd_7975678 4095356359490151356845531 := by
  unfold tailWord_7975678
  simp only [CollatzResearch.WordTrace]
  refine ⟨36362109349936027275276961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193931249866325478801477125 36362109349936027275276961)
  ·
    refine ⟨27271582012452020456457721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36362109349936027275276961 27271582012452020456457721)
    ·
      refine ⟨20453686509339015342343291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27271582012452020456457721 20453686509339015342343291)
      ·
        refine ⟨30680529764008523013514937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20453686509339015342343291 30680529764008523013514937)
        ·
          refine ⟨23010397323006392260136203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30680529764008523013514937 23010397323006392260136203)
          ·
            refine ⟨34515595984509588390204305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23010397323006392260136203 34515595984509588390204305)
            ·
              refine ⟨25886696988382191292653229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34515595984509588390204305 25886696988382191292653229)
              ·
                refine ⟨9707511370643321734744961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25886696988382191292653229 9707511370643321734744961)
                ·
                  refine ⟨7280633527982491301058721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9707511370643321734744961 7280633527982491301058721)
                  ·
                    refine ⟨5460475145986868475794041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7280633527982491301058721 5460475145986868475794041)
                    ·
                      refine ⟨4095356359490151356845531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460475145986868475794041 4095356359490151356845531)
                      ·
                        rfl

theorem cell23_7975678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_7975678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975678 prefixEnd_7975678 := by exact prefixLift 7975678
  have htrace : WordTrace (prefixWord ++ tailWord_7975678) baseStart_7975678 baseEnd_7975678 := by
    simpa [prefixWord, tailWord_7975678, baseEnd_7975678] using wordTrace_append hprefix tailTrace_7975678
  have hstable : (prefixWord ++ tailWord_7975678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975678).length < 2 ^ (prefixWord ++ tailWord_7975678).sum := by decide
  have hdescent : baseEnd_7975678 < baseStart_7975678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975697 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 2, 5]
def baseStart_7975697 : Nat := 118140960795 + 7975697 * 2 ^ 59
def prefixEnd_7975697 : Nat := 4983230072969 + 3 ^ 40 * 7975697 * 2
def baseEnd_7975697 : Nat := 1365122038540862260835981

theorem tailTrace_7975697 : CollatzResearch.WordTrace tailWord_7975697 prefixEnd_7975697 1365122038540862260835981 := by
  unfold tailWord_7975697
  simp only [CollatzResearch.WordTrace]
  refine ⟨290897567786419384447157345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193931711857612922964771563 290897567786419384447157345)
  ·
    refine ⟨218173175839814538335368009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290897567786419384447157345 218173175839814538335368009)
    ·
      refine ⟨163629881879860903751526007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218173175839814538335368009 163629881879860903751526007)
      ·
        refine ⟨245444822819791355627289011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163629881879860903751526007 245444822819791355627289011)
        ·
          refine ⟨368167234229687033440933517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245444822819791355627289011 368167234229687033440933517)
          ·
            refine ⟨138062712836132637540350069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368167234229687033440933517 138062712836132637540350069)
            ·
              refine ⟨12943379328387434769407819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138062712836132637540350069 12943379328387434769407819)
              ·
                refine ⟨19415068992581152154111729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12943379328387434769407819 19415068992581152154111729)
                ·
                  refine ⟨14561301744435864115583797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19415068992581152154111729 14561301744435864115583797)
                  ·
                    refine ⟨1365122038540862260835981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14561301744435864115583797 1365122038540862260835981)
                    ·
                      rfl

theorem cell23_7975697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_7975697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975697 prefixEnd_7975697 := by exact prefixLift 7975697
  have htrace : WordTrace (prefixWord ++ tailWord_7975697) baseStart_7975697 baseEnd_7975697 := by
    simpa [prefixWord, tailWord_7975697, baseEnd_7975697] using wordTrace_append hprefix tailTrace_7975697
  have hstable : (prefixWord ++ tailWord_7975697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975697).length < 2 ^ (prefixWord ++ tailWord_7975697).sum := by decide
  have hdescent : baseEnd_7975697 < baseStart_7975697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975717 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_7975717 : Nat := 118140960795 + 7975717 * 2 ^ 59
def prefixEnd_7975717 : Nat := 4983230072969 + 3 ^ 40 * 7975717 * 2
def baseEnd_7975717 : Nat := 4095376385235676704257851

theorem tailTrace_7975717 : CollatzResearch.WordTrace tailWord_7975717 prefixEnd_7975717 4095376385235676704257851 := by
  unfold tailWord_7975717
  simp only [CollatzResearch.WordTrace]
  refine ⟨290898297246346927862885405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193932198164231285241923603 290898297246346927862885405)
  ·
    refine ⟨109086861467380097948582027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290898297246346927862885405 109086861467380097948582027)
    ·
      refine ⟨163630292201070146922873041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109086861467380097948582027 163630292201070146922873041)
      ·
        refine ⟨122722719150802610192154781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163630292201070146922873041 122722719150802610192154781)
        ·
          refine ⟨46021019681550978822058043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122722719150802610192154781 46021019681550978822058043)
          ·
            refine ⟨69031529522326468233087065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46021019681550978822058043 69031529522326468233087065)
            ·
              refine ⟨51773647141744851174815299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69031529522326468233087065 51773647141744851174815299)
              ·
                refine ⟨77660470712617276762222949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51773647141744851174815299 77660470712617276762222949)
                ·
                  refine ⟨14561338258615739392916803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77660470712617276762222949 14561338258615739392916803)
                  ·
                    refine ⟨21842007387923609089375205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14561338258615739392916803 21842007387923609089375205)
                    ·
                      refine ⟨4095376385235676704257851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21842007387923609089375205 4095376385235676704257851)
                      ·
                        rfl

theorem cell23_7975717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_7975717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975717 prefixEnd_7975717 := by exact prefixLift 7975717
  have htrace : WordTrace (prefixWord ++ tailWord_7975717) baseStart_7975717 baseEnd_7975717 := by
    simpa [prefixWord, tailWord_7975717, baseEnd_7975717] using wordTrace_append hprefix tailTrace_7975717
  have hstable : (prefixWord ++ tailWord_7975717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975717).length < 2 ^ (prefixWord ++ tailWord_7975717).sum := by decide
  have hdescent : baseEnd_7975717 < baseStart_7975717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975778 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_7975778 : Nat := 118140960795 + 7975778 * 2 ^ 59
def prefixEnd_7975778 : Nat := 4983230072969 + 3 ^ 40 * 7975778 * 2
def baseEnd_7975778 : Nat := 1365135902518533655198357

theorem tailTrace_7975778 : CollatzResearch.WordTrace tailWord_7975778 prefixEnd_7975778 1365135902518533655198357 := by
  unfold tailWord_7975778
  simp only [CollatzResearch.WordTrace]
  refine ⟨72725130524781483820213997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193933681399417290187237325 72725130524781483820213997)
  ·
    refine ⟨27271923946793056432580249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72725130524781483820213997 27271923946793056432580249)
    ·
      refine ⟨20453942960094792324435187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27271923946793056432580249 20453942960094792324435187)
      ·
        refine ⟨30680914440142188486652781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20453942960094792324435187 30680914440142188486652781)
        ·
          refine ⟨11505342915053320682494793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30680914440142188486652781 11505342915053320682494793)
          ·
            refine ⟨8629007186289990511871095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11505342915053320682494793 8629007186289990511871095)
            ·
              refine ⟨12943510779434985767806643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8629007186289990511871095 12943510779434985767806643)
              ·
                refine ⟨19415266169152478651709965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12943510779434985767806643 19415266169152478651709965)
                ·
                  refine ⟨7280724813432179494391237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19415266169152478651709965 7280724813432179494391237)
                  ·
                    refine ⟨1365135902518533655198357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7280724813432179494391237 1365135902518533655198357)
                    ·
                      rfl

theorem cell23_7975778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_7975778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975778 prefixEnd_7975778 := by exact prefixLift 7975778
  have htrace : WordTrace (prefixWord ++ tailWord_7975778) baseStart_7975778 baseEnd_7975778 := by
    simpa [prefixWord, tailWord_7975778, baseEnd_7975778] using wordTrace_append hprefix tailTrace_7975778
  have hstable : (prefixWord ++ tailWord_7975778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975778).length < 2 ^ (prefixWord ++ tailWord_7975778).sum := by decide
  have hdescent : baseEnd_7975778 < baseStart_7975778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975794 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 3, 5, 2]
def baseStart_7975794 : Nat := 118140960795 + 7975794 * 2 ^ 59
def prefixEnd_7975794 : Nat := 4983230072969 + 3 ^ 40 * 7975794 * 2
def baseEnd_7975794 : Nat := 4095415923246072902994997

theorem tailTrace_7975794 : CollatzResearch.WordTrace tailWord_7975794 prefixEnd_7975794 4095415923246072902994997 := by
  unfold tailWord_7975794
  simp only [CollatzResearch.WordTrace]
  refine ⟨72725276416766992503359609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193934070444711980008958957 72725276416766992503359609)
  ·
    refine ⟨54543957312575244377519707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72725276416766992503359609 54543957312575244377519707)
    ·
      refine ⟨81815935968862866566279561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54543957312575244377519707 81815935968862866566279561)
      ·
        refine ⟨61361951976647149924709671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81815935968862866566279561 61361951976647149924709671)
        ·
          refine ⟨92042927964970724887064507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61361951976647149924709671 92042927964970724887064507)
          ·
            refine ⟨138064391947456087330596761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92042927964970724887064507 138064391947456087330596761)
            ·
              refine ⟨103548293960592065497947571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138064391947456087330596761 103548293960592065497947571)
              ·
                refine ⟨155322440940888098246921357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103548293960592065497947571 155322440940888098246921357)
                ·
                  refine ⟨58245915352833036842595509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155322440940888098246921357 58245915352833036842595509)
                  ·
                    refine ⟨5460554564328097203993329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58245915352833036842595509 5460554564328097203993329)
                    ·
                      refine ⟨4095415923246072902994997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460554564328097203993329 4095415923246072902994997)
                      ·
                        rfl

theorem cell23_7975794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_7975794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975794 prefixEnd_7975794 := by exact prefixLift 7975794
  have htrace : WordTrace (prefixWord ++ tailWord_7975794) baseStart_7975794 baseEnd_7975794 := by
    simpa [prefixWord, tailWord_7975794, baseEnd_7975794] using wordTrace_append hprefix tailTrace_7975794
  have hstable : (prefixWord ++ tailWord_7975794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975794).length < 2 ^ (prefixWord ++ tailWord_7975794).sum := by decide
  have hdescent : baseEnd_7975794 < baseStart_7975794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975811 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 2, 3, 2]
def baseStart_7975811 : Nat := 118140960795 + 7975811 * 2 ^ 59
def prefixEnd_7975811 : Nat := 4983230072969 + 3 ^ 40 * 7975811 * 2
def baseEnd_7975811 : Nat := 4095424652417199336482419

theorem tailTrace_7975811 : CollatzResearch.WordTrace tailWord_7975811 prefixEnd_7975811 4095424652417199336482419 := by
  unfold tailWord_7975811
  simp only [CollatzResearch.WordTrace]
  refine ⟨290901725708006381916807287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193934483805337587944538191 290901725708006381916807287)
  ·
    refine ⟨436352588562009572875210931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290901725708006381916807287 436352588562009572875210931)
    ·
      refine ⟨654528882843014359312816397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436352588562009572875210931 654528882843014359312816397)
      ·
        refine ⟨245448331066130384742306149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 654528882843014359312816397 245448331066130384742306149)
        ·
          refine ⟨46021562074899447139182403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245448331066130384742306149 46021562074899447139182403)
          ·
            refine ⟨69032343112349170708773605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46021562074899447139182403 69032343112349170708773605)
            ·
              refine ⟨12943564333565469507895051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69032343112349170708773605 12943564333565469507895051)
              ·
                refine ⟨19415346500348204261842577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12943564333565469507895051 19415346500348204261842577)
                ·
                  refine ⟨14561509875261153196381933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19415346500348204261842577 14561509875261153196381933)
                  ·
                    refine ⟨5460566203222932448643225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14561509875261153196381933 5460566203222932448643225)
                    ·
                      refine ⟨4095424652417199336482419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460566203222932448643225 4095424652417199336482419)
                      ·
                        rfl

theorem cell23_7975811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 3, 2].length) (baseStart_7975811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975811 prefixEnd_7975811 := by exact prefixLift 7975811
  have htrace : WordTrace (prefixWord ++ tailWord_7975811) baseStart_7975811 baseEnd_7975811 := by
    simpa [prefixWord, tailWord_7975811, baseEnd_7975811] using wordTrace_append hprefix tailTrace_7975811
  have hstable : (prefixWord ++ tailWord_7975811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975811).length < 2 ^ (prefixWord ++ tailWord_7975811).sum := by decide
  have hdescent : baseEnd_7975811 < baseStart_7975811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975817 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 3, 6]
def baseStart_7975817 : Nat := 118140960795 + 7975817 * 2 ^ 59
def prefixEnd_7975817 : Nat := 4983230072969 + 3 ^ 40 * 7975817 * 2
def baseEnd_7975817 : Nat := 1365142577767042104335797

theorem tailTrace_7975817 : CollatzResearch.WordTrace tailWord_7975817 prefixEnd_7975817 1365142577767042104335797 := by
  unfold tailWord_7975817
  simp only [CollatzResearch.WordTrace]
  refine ⟨290901944545984644941525705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193934629697323096627683803 290901944545984644941525705)
  ·
    refine ⟨218176458409488483706144279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290901944545984644941525705 218176458409488483706144279)
    ·
      refine ⟨327264687614232725559216419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218176458409488483706144279 327264687614232725559216419)
      ·
        refine ⟨490897031421349088338824629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327264687614232725559216419 490897031421349088338824629)
        ·
          refine ⟨46021596695751477031764809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 490897031421349088338824629 46021596695751477031764809)
          ·
            refine ⟨34516197521813607773823607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46021596695751477031764809 34516197521813607773823607)
            ·
              refine ⟨51774296282720411660735411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34516197521813607773823607 51774296282720411660735411)
              ·
                refine ⟨77661444424080617491103117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51774296282720411660735411 77661444424080617491103117)
                ·
                  refine ⟨29123041659030231559163669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77661444424080617491103117 29123041659030231559163669)
                  ·
                    refine ⟨1365142577767042104335797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29123041659030231559163669 1365142577767042104335797)
                    ·
                      rfl

theorem cell23_7975817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_7975817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975817 prefixEnd_7975817 := by exact prefixLift 7975817
  have htrace : WordTrace (prefixWord ++ tailWord_7975817) baseStart_7975817 baseEnd_7975817 := by
    simpa [prefixWord, tailWord_7975817, baseEnd_7975817] using wordTrace_append hprefix tailTrace_7975817
  have hstable : (prefixWord ++ tailWord_7975817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975817).length < 2 ^ (prefixWord ++ tailWord_7975817).sum := by decide
  have hdescent : baseEnd_7975817 < baseStart_7975817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975827 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 5]
def baseStart_7975827 : Nat := 118140960795 + 7975827 * 2 ^ 59
def prefixEnd_7975827 : Nat := 4983230072969 + 3 ^ 40 * 7975827 * 2
def baseEnd_7975827 : Nat := 4095432868107671273882345

theorem tailTrace_7975827 : CollatzResearch.WordTrace tailWord_7975827 prefixEnd_7975827 4095432868107671273882345 := by
  unfold tailWord_7975827
  simp only [CollatzResearch.WordTrace]
  refine ⟨290902309275948416649389735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193934872850632277766259823 290902309275948416649389735)
  ·
    refine ⟨436353463913922624974084603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290902309275948416649389735 436353463913922624974084603)
    ·
      refine ⟨654530195870883937461126905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436353463913922624974084603 654530195870883937461126905)
      ·
        refine ⟨490897646903162953095845179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654530195870883937461126905 490897646903162953095845179)
        ·
          refine ⟨736346470354744429643767769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490897646903162953095845179 736346470354744429643767769)
          ·
            refine ⟨552259852766058322232825827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736346470354744429643767769 552259852766058322232825827)
            ·
              refine ⟨828389779149087483349238741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552259852766058322232825827 828389779149087483349238741)
              ·
                refine ⟨19415385448806737890997783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 828389779149087483349238741 19415385448806737890997783)
                ·
                  refine ⟨29123078173210106836496675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19415385448806737890997783 29123078173210106836496675)
                  ·
                    refine ⟨43684617259815160254745013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29123078173210106836496675 43684617259815160254745013)
                    ·
                      refine ⟨4095432868107671273882345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43684617259815160254745013 4095432868107671273882345)
                      ·
                        rfl

theorem cell23_7975827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_7975827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975827 prefixEnd_7975827 := by exact prefixLift 7975827
  have htrace : WordTrace (prefixWord ++ tailWord_7975827) baseStart_7975827 baseEnd_7975827 := by
    simpa [prefixWord, tailWord_7975827, baseEnd_7975827] using wordTrace_append hprefix tailTrace_7975827
  have hstable : (prefixWord ++ tailWord_7975827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975827).length < 2 ^ (prefixWord ++ tailWord_7975827).sum := by decide
  have hdescent : baseEnd_7975827 < baseStart_7975827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975844 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_7975844 : Nat := 118140960795 + 7975844 * 2 ^ 59
def prefixEnd_7975844 : Nat := 4983230072969 + 3 ^ 40 * 7975844 * 2
def baseEnd_7975844 : Nat := 4095441597278797707369767

theorem tailTrace_7975844 : CollatzResearch.WordTrace tailWord_7975844 prefixEnd_7975844 4095441597278797707369767 := by
  unfold tailWord_7975844
  simp only [CollatzResearch.WordTrace]
  refine ⟨145451464658443414276379293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193935286211257885701839057 145451464658443414276379293)
  ·
    refine ⟨54544299246916280353642235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145451464658443414276379293 54544299246916280353642235)
    ·
      refine ⟨81816448870374420530463353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54544299246916280353642235 81816448870374420530463353)
      ·
        refine ⟨61362336652780815397847515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81816448870374420530463353 61362336652780815397847515)
        ·
          refine ⟨92043504979171223096771273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61362336652780815397847515 92043504979171223096771273)
          ·
            refine ⟨69032628734378417322578455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92043504979171223096771273 69032628734378417322578455)
            ·
              refine ⟨103548943101567625983867683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69032628734378417322578455 103548943101567625983867683)
              ·
                refine ⟨155323414652351438975801525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103548943101567625983867683 155323414652351438975801525)
                ·
                  refine ⟨14561570123657947403981393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155323414652351438975801525 14561570123657947403981393)
                  ·
                    refine ⟨10921177592743460552986045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14561570123657947403981393 10921177592743460552986045)
                    ·
                      refine ⟨4095441597278797707369767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10921177592743460552986045 4095441597278797707369767)
                      ·
                        rfl

theorem cell23_7975844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_7975844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975844 prefixEnd_7975844 := by exact prefixLift 7975844
  have htrace : WordTrace (prefixWord ++ tailWord_7975844) baseStart_7975844 baseEnd_7975844 := by
    simpa [prefixWord, tailWord_7975844, baseEnd_7975844] using wordTrace_append hprefix tailTrace_7975844
  have hstable : (prefixWord ++ tailWord_7975844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975844).length < 2 ^ (prefixWord ++ tailWord_7975844).sum := by decide
  have hdescent : baseEnd_7975844 < baseStart_7975844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975861 : List Nat := [1, 3, 3, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_7975861 : Nat := 118140960795 + 7975861 * 2 ^ 59
def prefixEnd_7975861 : Nat := 4983230072969 + 3 ^ 40 * 7975861 * 2
def baseEnd_7975861 : Nat := 4095450326449924140857189

theorem tailTrace_7975861 : CollatzResearch.WordTrace tailWord_7975861 prefixEnd_7975861 4095450326449924140857189 := by
  unfold tailWord_7975861
  simp only [CollatzResearch.WordTrace]
  refine ⟨290903549357825240456127437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193935699571883493637418291 290903549357825240456127437)
  ·
    refine ⟨109088831009184465171047789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290903549357825240456127437 109088831009184465171047789)
    ·
      refine ⟨40908311628444174439142921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109088831009184465171047789 40908311628444174439142921)
      ·
        refine ⟨30681233721333130829357191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40908311628444174439142921 30681233721333130829357191)
        ·
          refine ⟨46021850581999696244035787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30681233721333130829357191 46021850581999696244035787)
          ·
            refine ⟨69032775872999544366053681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46021850581999696244035787 69032775872999544366053681)
            ·
              refine ⟨51774581904749658274540261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69032775872999544366053681 51774581904749658274540261)
              ·
                refine ⟨9707734107140560926476299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51774581904749658274540261 9707734107140560926476299)
                ·
                  refine ⟨14561601160710841389714449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9707734107140560926476299 14561601160710841389714449)
                  ·
                    refine ⟨10921200870533131042285837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14561601160710841389714449 10921200870533131042285837)
                    ·
                      refine ⟨4095450326449924140857189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10921200870533131042285837 4095450326449924140857189)
                      ·
                        rfl

theorem cell23_7975861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_7975861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975861 prefixEnd_7975861 := by exact prefixLift 7975861
  have htrace : WordTrace (prefixWord ++ tailWord_7975861) baseStart_7975861 baseEnd_7975861 := by
    simpa [prefixWord, tailWord_7975861, baseEnd_7975861] using wordTrace_append hprefix tailTrace_7975861
  have hstable : (prefixWord ++ tailWord_7975861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975861).length < 2 ^ (prefixWord ++ tailWord_7975861).sum := by decide
  have hdescent : baseEnd_7975861 < baseStart_7975861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975862 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7975862 : Nat := 118140960795 + 7975862 * 2 ^ 59
def prefixEnd_7975862 : Nat := 4983230072969 + 3 ^ 40 * 7975862 * 2
def baseEnd_7975862 : Nat := 4095450839930578636944685

theorem tailTrace_7975862 : CollatzResearch.WordTrace tailWord_7975862 prefixEnd_7975862 4095450839930578636944685 := by
  unfold tailWord_7975862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18181474114426351101682115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193935723887214411751275893 18181474114426351101682115)
  ·
    refine ⟨27272211171639526652523173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18181474114426351101682115 27272211171639526652523173)
    ·
      refine ⟨5113539594682411247348095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27272211171639526652523173 5113539594682411247348095)
      ·
        refine ⟨7670309392023616871022143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5113539594682411247348095 7670309392023616871022143)
        ·
          refine ⟨11505464088035425306533215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7670309392023616871022143 11505464088035425306533215)
          ·
            refine ⟨17258196132053137959799823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11505464088035425306533215 17258196132053137959799823)
            ·
              refine ⟨25887294198079706939699735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17258196132053137959799823 25887294198079706939699735)
              ·
                refine ⟨38830941297119560409549603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25887294198079706939699735 38830941297119560409549603)
                ·
                  refine ⟨58246411945679340614324405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38830941297119560409549603 58246411945679340614324405)
                  ·
                    refine ⟨5460601119907438182592913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58246411945679340614324405 5460601119907438182592913)
                    ·
                      refine ⟨4095450839930578636944685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460601119907438182592913 4095450839930578636944685)
                      ·
                        rfl

theorem cell23_7975862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7975862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975862 prefixEnd_7975862 := by exact prefixLift 7975862
  have htrace : WordTrace (prefixWord ++ tailWord_7975862) baseStart_7975862 baseEnd_7975862 := by
    simpa [prefixWord, tailWord_7975862, baseEnd_7975862] using wordTrace_append hprefix tailTrace_7975862
  have hstable : (prefixWord ++ tailWord_7975862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975862).length < 2 ^ (prefixWord ++ tailWord_7975862).sum := by decide
  have hdescent : baseEnd_7975862 < baseStart_7975862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975864 : List Nat := [2, 1, 2, 1, 2, 5, 3, 7]
def baseStart_7975864 : Nat := 118140960795 + 7975864 * 2 ^ 59
def prefixEnd_7975864 : Nat := 4983230072969 + 3 ^ 40 * 7975864 * 2
def baseEnd_7975864 : Nat := 151683402477477319597025

theorem tailTrace_7975864 : CollatzResearch.WordTrace tailWord_7975864 prefixEnd_7975864 151683402477477319597025 := by
  unfold tailWord_7975864
  simp only [CollatzResearch.WordTrace]
  refine ⟨145451829388407185984243323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193935772517876247978991097 145451829388407185984243323)
  ·
    refine ⟨218177744082610778976364985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145451829388407185984243323 218177744082610778976364985)
    ·
      refine ⟨163633308061958084232273739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218177744082610778976364985 163633308061958084232273739)
      ·
        refine ⟨245449962092937126348410609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163633308061958084232273739 245449962092937126348410609)
        ·
          refine ⟨184087471569702844761307957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245449962092937126348410609 184087471569702844761307957)
          ·
            refine ⟨17258200459659641696372621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184087471569702844761307957 17258200459659641696372621)
            ·
              refine ⟨6471825172372365636139733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17258200459659641696372621 6471825172372365636139733)
              ·
                refine ⟨151683402477477319597025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6471825172372365636139733 151683402477477319597025)
                ·
                  rfl

theorem cell23_7975864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 7].length) (baseStart_7975864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975864 prefixEnd_7975864 := by exact prefixLift 7975864
  have htrace : WordTrace (prefixWord ++ tailWord_7975864) baseStart_7975864 baseEnd_7975864 := by
    simpa [prefixWord, tailWord_7975864, baseEnd_7975864] using wordTrace_append hprefix tailTrace_7975864
  have hstable : (prefixWord ++ tailWord_7975864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975864).length < 2 ^ (prefixWord ++ tailWord_7975864).sum := by decide
  have hdescent : baseEnd_7975864 < baseStart_7975864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975948 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 4, 2, 2]
def baseStart_7975948 : Nat := 118140960795 + 7975948 * 2 ^ 59
def prefixEnd_7975948 : Nat := 4983230072969 + 3 ^ 40 * 7975948 * 2
def baseEnd_7975948 : Nat := 4095494999266865300469289

theorem tailTrace_7975948 : CollatzResearch.WordTrace tailWord_7975948 prefixEnd_7975948 4095494999266865300469289 := by
  unfold tailWord_7975948
  simp only [CollatzResearch.WordTrace]
  refine ⟨145453361254255027157272249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193937815005673369543029665 145453361254255027157272249)
  ·
    refine ⟨109090020940691270367954187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145453361254255027157272249 109090020940691270367954187)
    ·
      refine ⟨163635031411036905551931281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109090020940691270367954187 163635031411036905551931281)
      ·
        refine ⟨122726273558277679163948461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163635031411036905551931281 122726273558277679163948461)
        ·
          refine ⟨46022352584354129686480673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122726273558277679163948461 46022352584354129686480673)
          ·
            refine ⟨34516764438265597264860505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46022352584354129686480673 34516764438265597264860505)
            ·
              refine ⟨25887573328699197948645379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34516764438265597264860505 25887573328699197948645379)
              ·
                refine ⟨38831359993048796922968069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25887573328699197948645379 38831359993048796922968069)
                ·
                  refine ⟨7280879998696649423056513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38831359993048796922968069 7280879998696649423056513)
                  ·
                    refine ⟨5460659999022487067292385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7280879998696649423056513 5460659999022487067292385)
                    ·
                      refine ⟨4095494999266865300469289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460659999022487067292385 4095494999266865300469289)
                      ·
                        rfl

theorem cell23_7975948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_7975948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975948 prefixEnd_7975948 := by exact prefixLift 7975948
  have htrace : WordTrace (prefixWord ++ tailWord_7975948) baseStart_7975948 baseEnd_7975948 := by
    simpa [prefixWord, tailWord_7975948, baseEnd_7975948] using wordTrace_append hprefix tailTrace_7975948
  have hstable : (prefixWord ++ tailWord_7975948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975948).length < 2 ^ (prefixWord ++ tailWord_7975948).sum := by decide
  have hdescent : baseEnd_7975948 < baseStart_7975948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7975994 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_7975994 : Nat := 118140960795 + 7975994 * 2 ^ 59
def prefixEnd_7975994 : Nat := 4983230072969 + 3 ^ 40 * 7975994 * 2
def baseEnd_7975994 : Nat := 4095518619376972120494077

theorem tailTrace_7975994 : CollatzResearch.WordTrace tailWord_7975994 prefixEnd_7975994 4095518619376972120494077 := by
  unfold tailWord_7975994
  simp only [CollatzResearch.WordTrace]
  refine ⟨72727100066585851042679759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193938933510895602780479357 72727100066585851042679759)
  ·
    refine ⟨109090650099878776564019639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72727100066585851042679759 109090650099878776564019639)
    ·
      refine ⟨163635975149818164846029459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109090650099878776564019639 163635975149818164846029459)
      ·
        refine ⟨245453962724727247269044189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163635975149818164846029459 245453962724727247269044189)
        ·
          refine ⟨92045236021772717725891571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245453962724727247269044189 92045236021772717725891571)
          ·
            refine ⟨138067854032659076588837357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92045236021772717725891571 138067854032659076588837357)
            ·
              refine ⟨51775445262247153720814009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138067854032659076588837357 51775445262247153720814009)
              ·
                refine ⟨38831583946685365290610507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51775445262247153720814009 38831583946685365290610507)
                ·
                  refine ⟨58247375920028047935915761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38831583946685365290610507 58247375920028047935915761)
                  ·
                    refine ⟨43685531940021035951936821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58247375920028047935915761 43685531940021035951936821)
                    ·
                      refine ⟨4095518619376972120494077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43685531940021035951936821 4095518619376972120494077)
                      ·
                        rfl

theorem cell23_7975994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_7975994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7975994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7975994 prefixEnd_7975994 := by exact prefixLift 7975994
  have htrace : WordTrace (prefixWord ++ tailWord_7975994) baseStart_7975994 baseEnd_7975994 := by
    simpa [prefixWord, tailWord_7975994, baseEnd_7975994] using wordTrace_append hprefix tailTrace_7975994
  have hstable : (prefixWord ++ tailWord_7975994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7975994).length < 2 ^ (prefixWord ++ tailWord_7975994).sum := by decide
  have hdescent : baseEnd_7975994 < baseStart_7975994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7975994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976031 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 3, 4]
def baseStart_7976031 : Nat := 118140960795 + 7976031 * 2 ^ 59
def prefixEnd_7976031 : Nat := 4983230072969 + 3 ^ 40 * 7976031 * 2
def baseEnd_7976031 : Nat := 1365179206053729491910469

theorem tailTrace_7976031 : CollatzResearch.WordTrace tailWord_7976031 prefixEnd_7976031 1365179206053729491910469 := by
  unfold tailWord_7976031
  simp only [CollatzResearch.WordTrace]
  refine ⟨290909749767209359489815947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193939833178139572993210631 290909749767209359489815947)
  ·
    refine ⟨436364624650814039234723921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290909749767209359489815947 436364624650814039234723921)
    ·
      refine ⟨327273468488110529426042941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436364624650814039234723921 327273468488110529426042941)
      ·
        refine ⟨122727550683041448534766103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327273468488110529426042941 122727550683041448534766103)
        ·
          refine ⟨184091326024562172802149155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122727550683041448534766103 184091326024562172802149155)
          ·
            refine ⟨276136989036843259203223733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184091326024562172802149155 276136989036843259203223733)
            ·
              refine ⟨25887842722204055550302225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276136989036843259203223733 25887842722204055550302225)
              ·
                refine ⟨19415882041653041662726669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25887842722204055550302225 19415882041653041662726669)
                ·
                  refine ⟨7280955765619890623522501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19415882041653041662726669 7280955765619890623522501)
                  ·
                    refine ⟨1365179206053729491910469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7280955765619890623522501 1365179206053729491910469)
                    ·
                      rfl

theorem cell23_7976031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 4].length) (baseStart_7976031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976031 prefixEnd_7976031 := by exact prefixLift 7976031
  have htrace : WordTrace (prefixWord ++ tailWord_7976031) baseStart_7976031 baseEnd_7976031 := by
    simpa [prefixWord, tailWord_7976031, baseEnd_7976031] using wordTrace_append hprefix tailTrace_7976031
  have hstable : (prefixWord ++ tailWord_7976031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976031).length < 2 ^ (prefixWord ++ tailWord_7976031).sum := by decide
  have hdescent : baseEnd_7976031 < baseStart_7976031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976041 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 1, 4, 3]
def baseStart_7976041 : Nat := 118140960795 + 7976041 * 2 ^ 59
def prefixEnd_7976041 : Nat := 4983230072969 + 3 ^ 40 * 7976041 * 2
def baseEnd_7976041 : Nat := 4095542752967733436606361

theorem tailTrace_7976041 : CollatzResearch.WordTrace tailWord_7976041 prefixEnd_7976041 4095542752967733436606361 := by
  unfold tailWord_7976041
  simp only [CollatzResearch.WordTrace]
  refine ⟨290910114497173131197679977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193940076331448754131786651 290910114497173131197679977)
  ·
    refine ⟨218182585872879848398259983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290910114497173131197679977 218182585872879848398259983)
    ·
      refine ⟨327273878809319772597389975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218182585872879848398259983 327273878809319772597389975)
      ·
        refine ⟨490910818213979658896084963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327273878809319772597389975 490910818213979658896084963)
        ·
          refine ⟨736366227320969488344127445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490910818213979658896084963 736366227320969488344127445)
          ·
            refine ⟨17258583452835222383065487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 736366227320969488344127445 17258583452835222383065487)
            ·
              refine ⟨25887875179252833574598231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17258583452835222383065487 25887875179252833574598231)
              ·
                refine ⟨38831812768879250361897347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25887875179252833574598231 38831812768879250361897347)
                ·
                  refine ⟨58247719153318875542846021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38831812768879250361897347 58247719153318875542846021)
                  ·
                    refine ⟨10921447341247289164283629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58247719153318875542846021 10921447341247289164283629)
                    ·
                      refine ⟨4095542752967733436606361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10921447341247289164283629 4095542752967733436606361)
                      ·
                        rfl

theorem cell23_7976041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 4, 3].length) (baseStart_7976041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976041 prefixEnd_7976041 := by exact prefixLift 7976041
  have htrace : WordTrace (prefixWord ++ tailWord_7976041) baseStart_7976041 baseEnd_7976041 := by
    simpa [prefixWord, tailWord_7976041, baseEnd_7976041] using wordTrace_append hprefix tailTrace_7976041
  have hstable : (prefixWord ++ tailWord_7976041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976041).length < 2 ^ (prefixWord ++ tailWord_7976041).sum := by decide
  have hdescent : baseEnd_7976041 < baseStart_7976041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976044 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 8]
def baseStart_7976044 : Nat := 118140960795 + 7976044 * 2 ^ 59
def prefixEnd_7976044 : Nat := 4983230072969 + 3 ^ 40 * 7976044 * 2
def baseEnd_7976044 : Nat := 455060477045521880540983

theorem tailTrace_7976044 : CollatzResearch.WordTrace tailWord_7976044 prefixEnd_7976044 455060477045521880540983 := by
  unfold tailWord_7976044
  simp only [CollatzResearch.WordTrace]
  refine ⟨145455111958081131355019593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193940149277441508473359457 145455111958081131355019593)
  ·
    refine ⟨109091333968560848516264695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145455111958081131355019593 109091333968560848516264695)
    ·
      refine ⟨163637000952841272774397043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109091333968560848516264695 163637000952841272774397043)
      ·
        refine ⟨245455501429261909161595565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163637000952841272774397043 245455501429261909161595565)
        ·
          refine ⟨92045813035973215935598337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245455501429261909161595565 92045813035973215935598337)
          ·
            refine ⟨69034359776979911951698753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92045813035973215935598337 69034359776979911951698753)
            ·
              refine ⟨51775769832734933963774065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69034359776979911951698753 51775769832734933963774065)
              ·
                refine ⟨38831827374551200472830549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51775769832734933963774065 38831827374551200472830549)
                ·
                  refine ⟨455060477045521880540983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38831827374551200472830549 455060477045521880540983)
                  ·
                    rfl

theorem cell23_7976044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_7976044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976044 prefixEnd_7976044 := by exact prefixLift 7976044
  have htrace : WordTrace (prefixWord ++ tailWord_7976044) baseStart_7976044 baseEnd_7976044 := by
    simpa [prefixWord, tailWord_7976044, baseEnd_7976044] using wordTrace_append hprefix tailTrace_7976044
  have hstable : (prefixWord ++ tailWord_7976044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976044).length < 2 ^ (prefixWord ++ tailWord_7976044).sum := by decide
  have hdescent : baseEnd_7976044 < baseStart_7976044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976064 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 6]
def baseStart_7976064 : Nat := 118140960795 + 7976064 * 2 ^ 59
def prefixEnd_7976064 : Nat := 4983230072969 + 3 ^ 40 * 7976064 * 2
def baseEnd_7976064 : Nat := 4095554563022786846618755

theorem tailTrace_7976064 : CollatzResearch.WordTrace tailWord_7976064 prefixEnd_7976064 4095554563022786846618755 := by
  unfold tailWord_7976064
  simp only [CollatzResearch.WordTrace]
  refine ⟨145455476688044903062883623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193940635584059870750511497 145455476688044903062883623)
  ·
    refine ⟨218183215032067354594325435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145455476688044903062883623 218183215032067354594325435)
    ·
      refine ⟨327274822548101031891488153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218183215032067354594325435 327274822548101031891488153)
      ·
        refine ⟨245456116911075773918616115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327274822548101031891488153 245456116911075773918616115)
        ·
          refine ⟨368184175366613660877924173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245456116911075773918616115 368184175366613660877924173)
          ·
            refine ⟨138069065762480122829221565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368184175366613660877924173 138069065762480122829221565)
            ·
              refine ⟨51775899660930046060958087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138069065762480122829221565 51775899660930046060958087)
              ·
                refine ⟨77663849491395069091437131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51775899660930046060958087 77663849491395069091437131)
                ·
                  refine ⟨116495774237092603637155697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77663849491395069091437131 116495774237092603637155697)
                  ·
                    refine ⟨87371830677819452727866773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116495774237092603637155697 87371830677819452727866773)
                    ·
                      refine ⟨4095554563022786846618755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87371830677819452727866773 4095554563022786846618755)
                      ·
                        rfl

theorem cell23_7976064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_7976064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976064 prefixEnd_7976064 := by exact prefixLift 7976064
  have htrace : WordTrace (prefixWord ++ tailWord_7976064) baseStart_7976064 baseEnd_7976064 := by
    simpa [prefixWord, tailWord_7976064, baseEnd_7976064] using wordTrace_append hprefix tailTrace_7976064
  have hstable : (prefixWord ++ tailWord_7976064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976064).length < 2 ^ (prefixWord ++ tailWord_7976064).sum := by decide
  have hdescent : baseEnd_7976064 < baseStart_7976064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976065 : List Nat := [1, 2, 4, 2, 2, 1, 2, 4, 1, 4]
def baseStart_7976065 : Nat := 118140960795 + 7976065 * 2 ^ 59
def prefixEnd_7976065 : Nat := 4983230072969 + 3 ^ 40 * 7976065 * 2
def baseEnd_7976065 : Nat := 1365185025501147114235417

theorem tailTrace_7976065 : CollatzResearch.WordTrace tailWord_7976065 prefixEnd_7976065 1365185025501147114235417 := by
  unfold tailWord_7976065
  simp only [CollatzResearch.WordTrace]
  refine ⟨290910989849086183296553649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193940659899390788864369099 290910989849086183296553649)
  ·
    refine ⟨218183242386814637472415237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290910989849086183296553649 218183242386814637472415237)
    ·
      refine ⟨40909357947527744526077857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218183242386814637472415237 40909357947527744526077857)
      ·
        refine ⟨30682018460645808394558393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40909357947527744526077857 30682018460645808394558393)
        ·
          refine ⟨23011513845484356295918795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30682018460645808394558393 23011513845484356295918795)
          ·
            refine ⟨34517270768226534443878193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23011513845484356295918795 34517270768226534443878193)
            ·
              refine ⟨25887953076169900832908645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34517270768226534443878193 25887953076169900832908645)
              ·
                refine ⟨4853991201781856406170371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25887953076169900832908645 4853991201781856406170371)
                ·
                  refine ⟨7280986802672784609255557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4853991201781856406170371 7280986802672784609255557)
                  ·
                    refine ⟨1365185025501147114235417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7280986802672784609255557 1365185025501147114235417)
                    ·
                      rfl

theorem cell23_7976065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_7976065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976065 prefixEnd_7976065 := by exact prefixLift 7976065
  have htrace : WordTrace (prefixWord ++ tailWord_7976065) baseStart_7976065 baseEnd_7976065 := by
    simpa [prefixWord, tailWord_7976065, baseEnd_7976065] using wordTrace_append hprefix tailTrace_7976065
  have hstable : (prefixWord ++ tailWord_7976065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976065).length < 2 ^ (prefixWord ++ tailWord_7976065).sum := by decide
  have hdescent : baseEnd_7976065 < baseStart_7976065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976142 : List Nat := [4, 1, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_7976142 : Nat := 118140960795 + 7976142 * 2 ^ 59
def prefixEnd_7976142 : Nat := 4983230072969 + 3 ^ 40 * 7976142 * 2
def baseEnd_7976142 : Nat := 1365198204837945847147799

theorem tailTrace_7976142 : CollatzResearch.WordTrace tailWord_7976142 prefixEnd_7976142 1365198204837945847147799 := by
  unfold tailWord_7976142
  simp only [CollatzResearch.WordTrace]
  refine ⟨36364224783725903180888335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193942532179871483631404453 36364224783725903180888335)
  ·
    refine ⟨54546337175588854771332503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36364224783725903180888335 54546337175588854771332503)
    ·
      refine ⟨81819505763383282156998755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54546337175588854771332503 81819505763383282156998755)
      ·
        refine ⟨122729258645074923235498133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81819505763383282156998755 122729258645074923235498133)
        ·
          refine ⟨5752933998987887026663975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122729258645074923235498133 5752933998987887026663975)
          ·
            refine ⟨8629400998481830539995963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5752933998987887026663975 8629400998481830539995963)
            ·
              refine ⟨12944101497722745809993945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8629400998481830539995963 12944101497722745809993945)
              ·
                refine ⟨9708076123292059357495459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12944101497722745809993945 9708076123292059357495459)
                ·
                  refine ⟨14562114184938089036243189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9708076123292059357495459 14562114184938089036243189)
                  ·
                    refine ⟨1365198204837945847147799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14562114184938089036243189 1365198204837945847147799)
                    ·
                      rfl

theorem cell23_7976142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_7976142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976142 prefixEnd_7976142 := by exact prefixLift 7976142
  have htrace : WordTrace (prefixWord ++ tailWord_7976142) baseStart_7976142 baseEnd_7976142 := by
    simpa [prefixWord, tailWord_7976142, baseEnd_7976142] using wordTrace_append hprefix tailTrace_7976142
  have hstable : (prefixWord ++ tailWord_7976142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976142).length < 2 ^ (prefixWord ++ tailWord_7976142).sum := by decide
  have hdescent : baseEnd_7976142 < baseStart_7976142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976165 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 5]
def baseStart_7976165 : Nat := 118140960795 + 7976165 * 2 ^ 59
def prefixEnd_7976165 : Nat := 4983230072969 + 3 ^ 40 * 7976165 * 2
def baseEnd_7976165 : Nat := 4095606424568890951455791

theorem tailTrace_7976165 : CollatzResearch.WordTrace tailWord_7976165 prefixEnd_7976165 4095606424568890951455791 := by
  unfold tailWord_7976165
  simp only [CollatzResearch.WordTrace]
  refine ⟨290914637148723900375193949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193943091432482600250129299 290914637148723900375193949)
  ·
    refine ⟨109092988930771462640697731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290914637148723900375193949 109092988930771462640697731)
    ·
      refine ⟨163639483396157193961046597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109092988930771462640697731 163639483396157193961046597)
      ·
        refine ⟨30682403136779473867696237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163639483396157193961046597 30682403136779473867696237)
        ·
          refine ⟨11505901176292302700386089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30682403136779473867696237 11505901176292302700386089)
          ·
            refine ⟨8629425882219227025289567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11505901176292302700386089 8629425882219227025289567)
            ·
              refine ⟨12944138823328840537934351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8629425882219227025289567 12944138823328840537934351)
              ·
                refine ⟨19416208234993260806901527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12944138823328840537934351 19416208234993260806901527)
                ·
                  refine ⟨29124312352489891210352291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19416208234993260806901527 29124312352489891210352291)
                  ·
                    refine ⟨43686468528734836815528437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29124312352489891210352291 43686468528734836815528437)
                    ·
                      refine ⟨4095606424568890951455791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43686468528734836815528437 4095606424568890951455791)
                      ·
                        rfl

theorem cell23_7976165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_7976165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976165 prefixEnd_7976165 := by exact prefixLift 7976165
  have htrace : WordTrace (prefixWord ++ tailWord_7976165) baseStart_7976165 baseEnd_7976165 := by
    simpa [prefixWord, tailWord_7976165, baseEnd_7976165] using wordTrace_append hprefix tailTrace_7976165
  have hstable : (prefixWord ++ tailWord_7976165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976165).length < 2 ^ (prefixWord ++ tailWord_7976165).sum := by decide
  have hdescent : baseEnd_7976165 < baseStart_7976165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976179 : List Nat := [1, 1, 1, 2, 2, 5, 4, 2, 1, 2, 2]
def baseStart_7976179 : Nat := 118140960795 + 7976179 * 2 ^ 59
def prefixEnd_7976179 : Nat := 4983230072969 + 3 ^ 40 * 7976179 * 2
def baseEnd_7976179 : Nat := 4095613613298053896680727

theorem tailTrace_7976179 : CollatzResearch.WordTrace tailWord_7976179 prefixEnd_7976179 4095613613298053896680727 := by
  unfold tailWord_7976179
  simp only [CollatzResearch.WordTrace]
  refine ⟨290915147770673180766203591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193943431847115453844135727 290915147770673180766203591)
  ·
    refine ⟨436372721656009771149305387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290915147770673180766203591 436372721656009771149305387)
    ·
      refine ⟨654559082484014656723958081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436372721656009771149305387 654559082484014656723958081)
      ·
        refine ⟨490919311863010992542968561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654559082484014656723958081 490919311863010992542968561)
        ·
          refine ⟨368189483897258244407226421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490919311863010992542968561 368189483897258244407226421)
          ·
            refine ⟨34517764115367960413177477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 368189483897258244407226421 34517764115367960413177477)
            ·
              refine ⟨6472080771631492577470777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34517764115367960413177477 6472080771631492577470777)
              ·
                refine ⟨4854060578723619433103083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6472080771631492577470777 4854060578723619433103083)
                ·
                  refine ⟨7281090868085429149654625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854060578723619433103083 7281090868085429149654625)
                  ·
                    refine ⟨5460818151064071862240969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7281090868085429149654625 5460818151064071862240969)
                    ·
                      refine ⟨4095613613298053896680727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460818151064071862240969 4095613613298053896680727)
                      ·
                        rfl

theorem cell23_7976179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 1, 2, 2].length) (baseStart_7976179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976179 prefixEnd_7976179 := by exact prefixLift 7976179
  have htrace : WordTrace (prefixWord ++ tailWord_7976179) baseStart_7976179 baseEnd_7976179 := by
    simpa [prefixWord, tailWord_7976179, baseEnd_7976179] using wordTrace_append hprefix tailTrace_7976179
  have hstable : (prefixWord ++ tailWord_7976179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976179).length < 2 ^ (prefixWord ++ tailWord_7976179).sum := by decide
  have hdescent : baseEnd_7976179 < baseStart_7976179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976195 : List Nat := [1, 1, 1, 3, 2, 4, 2, 3, 2, 1, 3]
def baseStart_7976195 : Nat := 118140960795 + 7976195 * 2 ^ 59
def prefixEnd_7976195 : Nat := 4983230072969 + 3 ^ 40 * 7976195 * 2
def baseEnd_7976195 : Nat := 4095621828988525834080653

theorem tailTrace_7976195 : CollatzResearch.WordTrace tailWord_7976195 prefixEnd_7976195 4095621828988525834080653 := by
  unfold tailWord_7976195
  simp only [CollatzResearch.WordTrace]
  refine ⟨290915731338615215498786039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193943820892410143665857359 290915731338615215498786039)
  ·
    refine ⟨436373597007922823248179059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290915731338615215498786039 436373597007922823248179059)
    ·
      refine ⟨654560395511884234872268589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436373597007922823248179059 654560395511884234872268589)
      ·
        refine ⟨245460148316956588077100721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 654560395511884234872268589 245460148316956588077100721)
        ·
          refine ⟨184095111237717441057825541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245460148316956588077100721 184095111237717441057825541)
          ·
            refine ⟨34517833357072020198342289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184095111237717441057825541 34517833357072020198342289)
            ·
              refine ⟨25888375017804015148756717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34517833357072020198342289 25888375017804015148756717)
              ·
                refine ⟨9708140631676505680783769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25888375017804015148756717 9708140631676505680783769)
                ·
                  refine ⟨7281105473757379260587827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9708140631676505680783769 7281105473757379260587827)
                  ·
                    refine ⟨10921658210636068890881741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7281105473757379260587827 10921658210636068890881741)
                    ·
                      refine ⟨4095621828988525834080653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10921658210636068890881741 4095621828988525834080653)
                      ·
                        rfl

theorem cell23_7976195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_7976195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976195 prefixEnd_7976195 := by exact prefixLift 7976195
  have htrace : WordTrace (prefixWord ++ tailWord_7976195) baseStart_7976195 baseEnd_7976195 := by
    simpa [prefixWord, tailWord_7976195, baseEnd_7976195] using wordTrace_append hprefix tailTrace_7976195
  have hstable : (prefixWord ++ tailWord_7976195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976195).length < 2 ^ (prefixWord ++ tailWord_7976195).sum := by decide
  have hdescent : baseEnd_7976195 < baseStart_7976195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976201 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 2, 3, 4]
def baseStart_7976201 : Nat := 118140960795 + 7976201 * 2 ^ 59
def prefixEnd_7976201 : Nat := 4983230072969 + 3 ^ 40 * 7976201 * 2
def baseEnd_7976201 : Nat := 4095624909872452810605625

theorem tailTrace_7976201 : CollatzResearch.WordTrace tailWord_7976201 prefixEnd_7976201 4095624909872452810605625 := by
  unfold tailWord_7976201
  simp only [CollatzResearch.WordTrace]
  refine ⟨290915950176593478523504457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193943966784395652349002971 290915950176593478523504457)
  ·
    refine ⟨218186962632445108892628343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290915950176593478523504457 218186962632445108892628343)
    ·
      refine ⟨327280443948667663338942515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218186962632445108892628343 327280443948667663338942515)
      ·
        refine ⟨490920665923001495008413773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327280443948667663338942515 490920665923001495008413773)
        ·
          refine ⟨184095249721125560628155165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490920665923001495008413773 184095249721125560628155165)
          ·
            refine ⟨69035718645422085235558187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184095249721125560628155165 69035718645422085235558187)
            ·
              refine ⟨103553577968133127853337281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69035718645422085235558187 103553577968133127853337281)
              ·
                refine ⟨77665183476099845890002961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103553577968133127853337281 77665183476099845890002961)
                ·
                  refine ⟨58248887607074884417502221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77665183476099845890002961 58248887607074884417502221)
                  ·
                    refine ⟨21843332852653081656563333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58248887607074884417502221 21843332852653081656563333)
                    ·
                      refine ⟨4095624909872452810605625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21843332852653081656563333 4095624909872452810605625)
                      ·
                        rfl

theorem cell23_7976201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_7976201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976201 prefixEnd_7976201 := by exact prefixLift 7976201
  have htrace : WordTrace (prefixWord ++ tailWord_7976201) baseStart_7976201 baseEnd_7976201 := by
    simpa [prefixWord, tailWord_7976201, baseEnd_7976201] using wordTrace_append hprefix tailTrace_7976201
  have hstable : (prefixWord ++ tailWord_7976201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976201).length < 2 ^ (prefixWord ++ tailWord_7976201).sum := by decide
  have hdescent : baseEnd_7976201 < baseStart_7976201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976246 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_7976246 : Nat := 118140960795 + 7976246 * 2 ^ 59
def prefixEnd_7976246 : Nat := 4983230072969 + 3 ^ 40 * 7976246 * 2
def baseEnd_7976246 : Nat := 4095648016501905134542919

theorem tailTrace_7976246 : CollatzResearch.WordTrace tailWord_7976246 prefixEnd_7976246 4095648016501905134542919 := by
  unfold tailWord_7976246
  simp only [CollatzResearch.WordTrace]
  refine ⟨18182349466339403200555787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193945060974286967472595061 18182349466339403200555787)
  ·
    refine ⟨27273524199509104800833681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18182349466339403200555787 27273524199509104800833681)
    ·
      refine ⟨20455143149631828600625261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27273524199509104800833681 20455143149631828600625261)
      ·
        refine ⟨7670678681111935725234473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20455143149631828600625261 7670678681111935725234473)
        ·
          refine ⟨5753009010833951793925855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7670678681111935725234473 5753009010833951793925855)
          ·
            refine ⟨8629513516250927690888783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5753009010833951793925855 8629513516250927690888783)
            ·
              refine ⟨12944270274376391536333175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8629513516250927690888783 12944270274376391536333175)
              ·
                refine ⟨19416405411564587304499763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12944270274376391536333175 19416405411564587304499763)
                ·
                  refine ⟨29124608117346880956749645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19416405411564587304499763 29124608117346880956749645)
                  ·
                    refine ⟨10921728044005080358781117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29124608117346880956749645 10921728044005080358781117)
                    ·
                      refine ⟨4095648016501905134542919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10921728044005080358781117 4095648016501905134542919)
                      ·
                        rfl

theorem cell23_7976246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_7976246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976246 prefixEnd_7976246 := by exact prefixLift 7976246
  have htrace : WordTrace (prefixWord ++ tailWord_7976246) baseStart_7976246 baseEnd_7976246 := by
    simpa [prefixWord, tailWord_7976246, baseEnd_7976246] using wordTrace_append hprefix tailTrace_7976246
  have hstable : (prefixWord ++ tailWord_7976246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976246).length < 2 ^ (prefixWord ++ tailWord_7976246).sum := by decide
  have hdescent : baseEnd_7976246 < baseStart_7976246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976252 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 1, 4, 2]
def baseStart_7976252 : Nat := 118140960795 + 7976252 * 2 ^ 59
def prefixEnd_7976252 : Nat := 4983230072969 + 3 ^ 40 * 7976252 * 2
def baseEnd_7976252 : Nat := 4095651097385832111067891

theorem tailTrace_7976252 : CollatzResearch.WordTrace tailWord_7976252 prefixEnd_7976252 4095651097385832111067891 := by
  unfold tailWord_7976252
  simp only [CollatzResearch.WordTrace]
  refine ⟨145458905149704357116805505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193945206866272476155740673 145458905149704357116805505)
  ·
    refine ⟨109094178862278267837604129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145458905149704357116805505 109094178862278267837604129)
    ·
      refine ⟨81820634146708700878203097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109094178862278267837604129 81820634146708700878203097)
      ·
        refine ⟨61365475610031525658652323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81820634146708700878203097 61365475610031525658652323)
        ·
          refine ⟨92048213415047288487978485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61365475610031525658652323 92048213415047288487978485)
          ·
            refine ⟨8629520007660683295747983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92048213415047288487978485 8629520007660683295747983)
            ·
              refine ⟨12944280011491024943621975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8629520007660683295747983 12944280011491024943621975)
              ·
                refine ⟨19416420017236537415432963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12944280011491024943621975 19416420017236537415432963)
                ·
                  refine ⟨29124630025854806123149445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19416420017236537415432963 29124630025854806123149445)
                  ·
                    refine ⟨5460868129847776148090521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29124630025854806123149445 5460868129847776148090521)
                    ·
                      refine ⟨4095651097385832111067891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5460868129847776148090521 4095651097385832111067891)
                      ·
                        rfl

theorem cell23_7976252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_7976252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976252 prefixEnd_7976252 := by exact prefixLift 7976252
  have htrace : WordTrace (prefixWord ++ tailWord_7976252) baseStart_7976252 baseEnd_7976252 := by
    simpa [prefixWord, tailWord_7976252, baseEnd_7976252] using wordTrace_append hprefix tailTrace_7976252
  have hstable : (prefixWord ++ tailWord_7976252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976252).length < 2 ^ (prefixWord ++ tailWord_7976252).sum := by decide
  have hdescent : baseEnd_7976252 < baseStart_7976252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976288 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 4, 5]
def baseStart_7976288 : Nat := 118140960795 + 7976288 * 2 ^ 59
def prefixEnd_7976288 : Nat := 4983230072969 + 3 ^ 40 * 7976288 * 2
def baseEnd_7976288 : Nat := 1365223194229797990072575

theorem tailTrace_7976288 : CollatzResearch.WordTrace tailWord_7976288 prefixEnd_7976288 1365223194229797990072575 := by
  unfold tailWord_7976288
  simp only [CollatzResearch.WordTrace]
  refine ⟨145459561663639146190960759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193946082218185528254614345 145459561663639146190960759)
  ·
    refine ⟨218189342495458719286441139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145459561663639146190960759 218189342495458719286441139)
    ·
      refine ⟨327284013743188078929661709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218189342495458719286441139 327284013743188078929661709)
      ·
        refine ⟨122731505153695529598623141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327284013743188078929661709 122731505153695529598623141)
        ·
          refine ⟨23012157216317911799741839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122731505153695529598623141 23012157216317911799741839)
          ·
            refine ⟨34518235824476867699612759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23012157216317911799741839 34518235824476867699612759)
            ·
              refine ⟨51777353736715301549419139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34518235824476867699612759 51777353736715301549419139)
              ·
                refine ⟨77666030605072952324128709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51777353736715301549419139 77666030605072952324128709)
                ·
                  refine ⟨14562380738451178560774133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77666030605072952324128709 14562380738451178560774133)
                  ·
                    refine ⟨1365223194229797990072575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14562380738451178560774133 1365223194229797990072575)
                    ·
                      rfl

theorem cell23_7976288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4, 5].length) (baseStart_7976288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976288 prefixEnd_7976288 := by exact prefixLift 7976288
  have htrace : WordTrace (prefixWord ++ tailWord_7976288) baseStart_7976288 baseEnd_7976288 := by
    simpa [prefixWord, tailWord_7976288, baseEnd_7976288] using wordTrace_append hprefix tailTrace_7976288
  have hstable : (prefixWord ++ tailWord_7976288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976288).length < 2 ^ (prefixWord ++ tailWord_7976288).sum := by decide
  have hdescent : baseEnd_7976288 < baseStart_7976288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976292 : List Nat := [2, 3, 1, 1, 3, 3, 3, 2, 5]
def baseStart_7976292 : Nat := 118140960795 + 7976292 * 2 ^ 59
def prefixEnd_7976292 : Nat := 4983230072969 + 3 ^ 40 * 7976292 * 2
def baseEnd_7976292 : Nat := 455074626290223550507523

theorem tailTrace_7976292 : CollatzResearch.WordTrace tailWord_7976292 prefixEnd_7976292 455074626290223550507523 := by
  unfold tailWord_7976292
  simp only [CollatzResearch.WordTrace]
  refine ⟨145459634609631900532533565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193946179479509200710044753 145459634609631900532533565)
  ·
    refine ⟨54547362978611962699700087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145459634609631900532533565 54547362978611962699700087)
    ·
      refine ⟨81821044467917944049550131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54547362978611962699700087 81821044467917944049550131)
      ·
        refine ⟨122731566701876916074325197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81821044467917944049550131 122731566701876916074325197)
        ·
          refine ⟨46024337513203843527871949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122731566701876916074325197 46024337513203843527871949)
          ·
            refine ⟨17259126567451441322951981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46024337513203843527871949 17259126567451441322951981)
            ·
              refine ⟨6472172462794290496106993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17259126567451441322951981 6472172462794290496106993)
              ·
                refine ⟨4854129347095717872080245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6472172462794290496106993 4854129347095717872080245)
                ·
                  refine ⟨455074626290223550507523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4854129347095717872080245 455074626290223550507523)
                  ·
                    rfl

theorem cell23_7976292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_7976292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976292 prefixEnd_7976292 := by exact prefixLift 7976292
  have htrace : WordTrace (prefixWord ++ tailWord_7976292) baseStart_7976292 baseEnd_7976292 := by
    simpa [prefixWord, tailWord_7976292, baseEnd_7976292] using wordTrace_append hprefix tailTrace_7976292
  have hstable : (prefixWord ++ tailWord_7976292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976292).length < 2 ^ (prefixWord ++ tailWord_7976292).sum := by decide
  have hdescent : baseEnd_7976292 < baseStart_7976292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976322 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_7976322 : Nat := 118140960795 + 7976322 * 2 ^ 59
def prefixEnd_7976322 : Nat := 4983230072969 + 3 ^ 40 * 7976322 * 2
def baseEnd_7976322 : Nat := 1365229013677215612397523

theorem tailTrace_7976322 : CollatzResearch.WordTrace tailWord_7976322 prefixEnd_7976322 1365229013677215612397523 := by
  unfold tailWord_7976322
  simp only [CollatzResearch.WordTrace]
  refine ⟨72730090852288779047164805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193946908939436744125772813 72730090852288779047164805)
  ·
    refine ⟨13636892034804146071343401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72730090852288779047164805 13636892034804146071343401)
    ·
      refine ⟨10227669026103109553507551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13636892034804146071343401 10227669026103109553507551)
      ·
        refine ⟨15341503539154664330261327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10227669026103109553507551 15341503539154664330261327)
        ·
          refine ⟨23012255308731996495391991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15341503539154664330261327 23012255308731996495391991)
          ·
            refine ⟨34518382963097994743087987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23012255308731996495391991 34518382963097994743087987)
            ·
              refine ⟨51777574444646992114631981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34518382963097994743087987 51777574444646992114631981)
              ·
                refine ⟨19416590416742622042986993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51777574444646992114631981 19416590416742622042986993)
                ·
                  refine ⟨14562442812556966532240245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19416590416742622042986993 14562442812556966532240245)
                  ·
                    refine ⟨1365229013677215612397523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14562442812556966532240245 1365229013677215612397523)
                    ·
                      rfl

theorem cell23_7976322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_7976322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976322 prefixEnd_7976322 := by exact prefixLift 7976322
  have htrace : WordTrace (prefixWord ++ tailWord_7976322) baseStart_7976322 baseEnd_7976322 := by
    simpa [prefixWord, tailWord_7976322, baseEnd_7976322] using wordTrace_append hprefix tailTrace_7976322
  have hstable : (prefixWord ++ tailWord_7976322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976322).length < 2 ^ (prefixWord ++ tailWord_7976322).sum := by decide
  have hdescent : baseEnd_7976322 < baseStart_7976322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976345 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 2, 2, 3]
def baseStart_7976345 : Nat := 118140960795 + 7976345 * 2 ^ 59
def prefixEnd_7976345 : Nat := 4983230072969 + 3 ^ 40 * 7976345 * 2
def baseEnd_7976345 : Nat := 4095698851086700247204963

theorem tailTrace_7976345 : CollatzResearch.WordTrace tailWord_7976345 prefixEnd_7976345 4095698851086700247204963 := by
  unfold tailWord_7976345
  simp only [CollatzResearch.WordTrace]
  refine ⟨290921202288071791116746489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193947468192047860744497659 290921202288071791116746489)
  ·
    refine ⟨218190901716053843337559867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290921202288071791116746489 218190901716053843337559867)
    ·
      refine ⟨327286352574080765006339801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218190901716053843337559867 327286352574080765006339801)
      ·
        refine ⟨245464764430560573754754851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327286352574080765006339801 245464764430560573754754851)
        ·
          refine ⟨368197146645840860632132277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245464764430560573754754851 368197146645840860632132277)
          ·
            refine ⟨34518482498047580684262401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 368197146645840860632132277 34518482498047580684262401)
            ·
              refine ⟨25888861873535685513196801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34518482498047580684262401 25888861873535685513196801)
              ·
                refine ⟨19416646405151764134897601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25888861873535685513196801 19416646405151764134897601)
                ·
                  refine ⟨14562484803863823101173201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19416646405151764134897601 14562484803863823101173201)
                  ·
                    refine ⟨10921863602897867325879901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14562484803863823101173201 10921863602897867325879901)
                    ·
                      refine ⟨4095698851086700247204963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10921863602897867325879901 4095698851086700247204963)
                      ·
                        rfl

theorem cell23_7976345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_7976345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976345 prefixEnd_7976345 := by exact prefixLift 7976345
  have htrace : WordTrace (prefixWord ++ tailWord_7976345) baseStart_7976345 baseEnd_7976345 := by
    simpa [prefixWord, tailWord_7976345, baseEnd_7976345] using wordTrace_append hprefix tailTrace_7976345
  have hstable : (prefixWord ++ tailWord_7976345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976345).length < 2 ^ (prefixWord ++ tailWord_7976345).sum := by decide
  have hdescent : baseEnd_7976345 < baseStart_7976345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976352 : List Nat := [2, 1, 1, 4, 1, 2, 3, 4, 1, 4]
def baseStart_7976352 : Nat := 118140960795 + 7976352 * 2 ^ 59
def prefixEnd_7976352 : Nat := 4983230072969 + 3 ^ 40 * 7976352 * 2
def baseEnd_7976352 : Nat := 1365234148483760573272477

theorem tailTrace_7976352 : CollatzResearch.WordTrace tailWord_7976352 prefixEnd_7976352 1365234148483760573272477 := by
  unfold tailWord_7976352
  simp only [CollatzResearch.WordTrace]
  refine ⟨145460728799523215656125655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193947638399364287541500873 145460728799523215656125655)
  ·
    refine ⟨218191093199284823484188483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145460728799523215656125655 218191093199284823484188483)
    ·
      refine ⟨327286639798927235226282725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218191093199284823484188483 327286639798927235226282725)
      ·
        refine ⟨61366244962298856604928011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327286639798927235226282725 61366244962298856604928011)
        ·
          refine ⟨92049367443448284907392017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61366244962298856604928011 92049367443448284907392017)
          ·
            refine ⟨69037025582586213680544013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92049367443448284907392017 69037025582586213680544013)
            ·
              refine ⟨25888884593469830130204005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69037025582586213680544013 25888884593469830130204005)
              ·
                refine ⟨4854165861275593149413251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25888884593469830130204005 4854165861275593149413251)
                ·
                  refine ⟨7281248791913389724119877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854165861275593149413251 7281248791913389724119877)
                  ·
                    refine ⟨1365234148483760573272477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7281248791913389724119877 1365234148483760573272477)
                    ·
                      rfl

theorem cell23_7976352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 1, 4].length) (baseStart_7976352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976352 prefixEnd_7976352 := by exact prefixLift 7976352
  have htrace : WordTrace (prefixWord ++ tailWord_7976352) baseStart_7976352 baseEnd_7976352 := by
    simpa [prefixWord, tailWord_7976352, baseEnd_7976352] using wordTrace_append hprefix tailTrace_7976352
  have hstable : (prefixWord ++ tailWord_7976352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976352).length < 2 ^ (prefixWord ++ tailWord_7976352).sum := by decide
  have hdescent : baseEnd_7976352 < baseStart_7976352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976408 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 3, 6]
def baseStart_7976408 : Nat := 118140960795 + 7976408 * 2 ^ 59
def prefixEnd_7976408 : Nat := 4983230072969 + 3 ^ 40 * 7976408 * 2
def baseEnd_7976408 : Nat := 1365243733455977833572391

theorem tailTrace_7976408 : CollatzResearch.WordTrace tailWord_7976408 prefixEnd_7976408 1365243733455977833572391 := by
  unfold tailWord_7976408
  simp only [CollatzResearch.WordTrace]
  refine ⟨145461750043421776438144939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193949000057895701917526585 145461750043421776438144939)
  ·
    refine ⟨218192625065132664657217409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145461750043421776438144939 218192625065132664657217409)
    ·
      refine ⟨163644468798849498492913057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218192625065132664657217409 163644468798849498492913057)
      ·
        refine ⟨122733351599137123869684793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163644468798849498492913057 122733351599137123869684793)
        ·
          refine ⟨92050013699352842902263595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122733351599137123869684793 92050013699352842902263595)
          ·
            refine ⟨138075020549029264353395393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92050013699352842902263595 138075020549029264353395393)
            ·
              refine ⟨103556265411771948265046545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138075020549029264353395393 103556265411771948265046545)
              ·
                refine ⟨77667199058828961198784909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103556265411771948265046545 77667199058828961198784909)
                ·
                  refine ⟨29125199647060860449544341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77667199058828961198784909 29125199647060860449544341)
                  ·
                    refine ⟨1365243733455977833572391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29125199647060860449544341 1365243733455977833572391)
                    ·
                      rfl

theorem cell23_7976408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_7976408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976408 prefixEnd_7976408 := by exact prefixLift 7976408
  have htrace : WordTrace (prefixWord ++ tailWord_7976408) baseStart_7976408 baseEnd_7976408 := by
    simpa [prefixWord, tailWord_7976408, baseEnd_7976408] using wordTrace_append hprefix tailTrace_7976408
  have hstable : (prefixWord ++ tailWord_7976408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976408).length < 2 ^ (prefixWord ++ tailWord_7976408).sum := by decide
  have hdescent : baseEnd_7976408 < baseStart_7976408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976409 : List Nat := [1, 2, 1, 2, 4, 2, 2, 4, 1, 1, 3]
def baseStart_7976409 : Nat := 118140960795 + 7976409 * 2 ^ 59
def prefixEnd_7976409 : Nat := 4983230072969 + 3 ^ 40 * 7976409 * 2
def baseEnd_7976409 : Nat := 4095731713848587996804669

theorem tailTrace_7976409 : CollatzResearch.WordTrace tailWord_7976409 prefixEnd_7976409 4095731713848587996804669 := by
  unfold tailWord_7976409
  simp only [CollatzResearch.WordTrace]
  refine ⟨290923536559839930047076281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193949024373226620031384187 290923536559839930047076281)
  ·
    refine ⟨218192652419879947535307211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290923536559839930047076281 218192652419879947535307211)
    ·
      refine ⟨327288978629819921302960817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218192652419879947535307211 327288978629819921302960817)
      ·
        refine ⟨245466733972364940977220613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327288978629819921302960817 245466733972364940977220613)
        ·
          refine ⟨46025012619818426433228865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245466733972364940977220613 46025012619818426433228865)
          ·
            refine ⟨34518759464863819824921649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46025012619818426433228865 34518759464863819824921649)
            ·
              refine ⟨25889069598647864868691237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34518759464863819824921649 25889069598647864868691237)
              ·
                refine ⟨4854200549746474662879607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25889069598647864868691237 4854200549746474662879607)
                ·
                  refine ⟨7281300824619711994319411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854200549746474662879607 7281300824619711994319411)
                  ·
                    refine ⟨10921951236929567991479117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7281300824619711994319411 10921951236929567991479117)
                    ·
                      refine ⟨4095731713848587996804669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10921951236929567991479117 4095731713848587996804669)
                      ·
                        rfl

theorem cell23_7976409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 1, 1, 3].length) (baseStart_7976409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976409 prefixEnd_7976409 := by exact prefixLift 7976409
  have htrace : WordTrace (prefixWord ++ tailWord_7976409) baseStart_7976409 baseEnd_7976409 := by
    simpa [prefixWord, tailWord_7976409, baseEnd_7976409] using wordTrace_append hprefix tailTrace_7976409
  have hstable : (prefixWord ++ tailWord_7976409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976409).length < 2 ^ (prefixWord ++ tailWord_7976409).sum := by decide
  have hdescent : baseEnd_7976409 < baseStart_7976409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976429 : List Nat := [1, 5, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_7976429 : Nat := 118140960795 + 7976429 * 2 ^ 59
def prefixEnd_7976429 : Nat := 4983230072969 + 3 ^ 40 * 7976429 * 2
def baseEnd_7976429 : Nat := 1365247327820559306184859

theorem tailTrace_7976429 : CollatzResearch.WordTrace tailWord_7976429 prefixEnd_7976429 1365247327820559306184859 := by
  unfold tailWord_7976429
  simp only [CollatzResearch.WordTrace]
  refine ⟨290924266019767473462804341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193949510679844982308536227 290924266019767473462804341)
  ·
    refine ⟨27274149939353200637137907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 290924266019767473462804341 27274149939353200637137907)
    ·
      refine ⟨40911224909029800955706861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27274149939353200637137907 40911224909029800955706861)
      ·
        refine ⟨15341709340886175358390073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40911224909029800955706861 15341709340886175358390073)
        ·
          refine ⟨11506282005664631518792555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15341709340886175358390073 11506282005664631518792555)
          ·
            refine ⟨17259423008496947278188833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11506282005664631518792555 17259423008496947278188833)
            ·
              refine ⟨12944567256372710458641625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17259423008496947278188833 12944567256372710458641625)
              ·
                refine ⟨9708425442279532843981219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12944567256372710458641625 9708425442279532843981219)
                ·
                  refine ⟨14562638163419299265971829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9708425442279532843981219 14562638163419299265971829)
                  ·
                    refine ⟨1365247327820559306184859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14562638163419299265971829 1365247327820559306184859)
                    ·
                      rfl

theorem cell23_7976429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_7976429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976429 prefixEnd_7976429 := by exact prefixLift 7976429
  have htrace : WordTrace (prefixWord ++ tailWord_7976429) baseStart_7976429 baseEnd_7976429 := by
    simpa [prefixWord, tailWord_7976429, baseEnd_7976429] using wordTrace_append hprefix tailTrace_7976429
  have hstable : (prefixWord ++ tailWord_7976429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976429).length < 2 ^ (prefixWord ++ tailWord_7976429).sum := by decide
  have hdescent : baseEnd_7976429 < baseStart_7976429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976432 : List Nat := [2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 4]
def baseStart_7976432 : Nat := 118140960795 + 7976432 * 2 ^ 59
def prefixEnd_7976432 : Nat := 4983230072969 + 3 ^ 40 * 7976432 * 2
def baseEnd_7976432 : Nat := 4095743523903641406817063

theorem tailTrace_7976432 : CollatzResearch.WordTrace tailWord_7976432 prefixEnd_7976432 4095743523903641406817063 := by
  unfold tailWord_7976432
  simp only [CollatzResearch.WordTrace]
  refine ⟨145462187719378302487581775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193949583625837736650109033 145462187719378302487581775)
  ·
    refine ⟨218193281579067453731372663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145462187719378302487581775 218193281579067453731372663)
    ·
      refine ⟨327289922368601180597058995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218193281579067453731372663 327289922368601180597058995)
      ·
        refine ⟨490934883552901770895588493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327289922368601180597058995 490934883552901770895588493)
        ·
          refine ⟨184100581332338164085845685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490934883552901770895588493 184100581332338164085845685)
          ·
            refine ⟨17259429499906702883048033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184100581332338164085845685 17259429499906702883048033)
            ·
              refine ⟨12944572124930027162286025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17259429499906702883048033 12944572124930027162286025)
              ·
                refine ⟨9708429093697520371714519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12944572124930027162286025 9708429093697520371714519)
                ·
                  refine ⟨14562643640546280557571779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9708429093697520371714519 14562643640546280557571779)
                  ·
                    refine ⟨21843965460819420836357669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14562643640546280557571779 21843965460819420836357669)
                    ·
                      refine ⟨4095743523903641406817063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21843965460819420836357669 4095743523903641406817063)
                      ·
                        rfl

theorem cell23_7976432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 4].length) (baseStart_7976432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976432 prefixEnd_7976432 := by exact prefixLift 7976432
  have htrace : WordTrace (prefixWord ++ tailWord_7976432) baseStart_7976432 baseEnd_7976432 := by
    simpa [prefixWord, tailWord_7976432, baseEnd_7976432] using wordTrace_append hprefix tailTrace_7976432
  have hstable : (prefixWord ++ tailWord_7976432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976432).length < 2 ^ (prefixWord ++ tailWord_7976432).sum := by decide
  have hdescent : baseEnd_7976432 < baseStart_7976432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976455 : List Nat := [1, 1, 4, 3, 2, 3, 9]
def baseStart_7976455 : Nat := 118140960795 + 7976455 * 2 ^ 59
def prefixEnd_7976455 : Nat := 4983230072969 + 3 ^ 40 * 7976455 * 2
def baseEnd_7976455 : Nat := 50564880666156726133697

theorem tailTrace_7976455 : CollatzResearch.WordTrace tailWord_7976455 prefixEnd_7976455 50564880666156726133697 := by
  unfold tailWord_7976455
  simp only [CollatzResearch.WordTrace]
  refine ⟨290925214317673279903250819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193950142878448853268833879 290925214317673279903250819)
  ·
    refine ⟨436387821476509919854876229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290925214317673279903250819 436387821476509919854876229)
    ·
      refine ⟨81822716526845609972789293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 436387821476509919854876229 81822716526845609972789293)
      ·
        refine ⟨30683518697567103739795985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81822716526845609972789293 30683518697567103739795985)
        ·
          refine ⟨23012639023175327804846989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30683518697567103739795985 23012639023175327804846989)
          ·
            refine ⟨8629739633690747926817621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23012639023175327804846989 8629739633690747926817621)
            ·
              refine ⟨50564880666156726133697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8629739633690747926817621 50564880666156726133697)
              ·
                rfl

theorem cell23_7976455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 9].length) (baseStart_7976455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976455 prefixEnd_7976455 := by exact prefixLift 7976455
  have htrace : WordTrace (prefixWord ++ tailWord_7976455) baseStart_7976455 baseEnd_7976455 := by
    simpa [prefixWord, tailWord_7976455, baseEnd_7976455] using wordTrace_append hprefix tailTrace_7976455
  have hstable : (prefixWord ++ tailWord_7976455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976455).length < 2 ^ (prefixWord ++ tailWord_7976455).sum := by decide
  have hdescent : baseEnd_7976455 < baseStart_7976455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976522 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 3, 4, 2]
def baseStart_7976522 : Nat := 118140960795 + 7976522 * 2 ^ 59
def prefixEnd_7976522 : Nat := 4983230072969 + 3 ^ 40 * 7976522 * 2
def baseEnd_7976522 : Nat := 4095789737162546054691649

theorem tailTrace_7976522 : CollatzResearch.WordTrace tailWord_7976522 prefixEnd_7976522 4095789737162546054691649 := by
  unfold tailWord_7976522
  simp only [CollatzResearch.WordTrace]
  refine ⟨72731914502107637586484955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193951772005620366897293213 72731914502107637586484955)
  ·
    refine ⟨109097871753161456379727433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72731914502107637586484955 109097871753161456379727433)
    ·
      refine ⟨81823403814871092284795575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109097871753161456379727433 81823403814871092284795575)
      ·
        refine ⟨122735105722306638427193363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81823403814871092284795575 122735105722306638427193363)
        ·
          refine ⟨184102658583459957640790045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122735105722306638427193363 184102658583459957640790045)
          ·
            refine ⟨69038496968797484115296267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184102658583459957640790045 69038496968797484115296267)
            ·
              refine ⟨103557745453196226172944401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69038496968797484115296267 103557745453196226172944401)
              ·
                refine ⟨77668309089897169629708301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103557745453196226172944401 77668309089897169629708301)
                ·
                  refine ⟨29125615908711438611140613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77668309089897169629708301 29125615908711438611140613)
                  ·
                    refine ⟨5461052982883394739588865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29125615908711438611140613 5461052982883394739588865)
                    ·
                      refine ⟨4095789737162546054691649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461052982883394739588865 4095789737162546054691649)
                      ·
                        rfl

theorem cell23_7976522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_7976522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976522 prefixEnd_7976522 := by exact prefixLift 7976522
  have htrace : WordTrace (prefixWord ++ tailWord_7976522) baseStart_7976522 baseEnd_7976522 := by
    simpa [prefixWord, tailWord_7976522, baseEnd_7976522] using wordTrace_append hprefix tailTrace_7976522
  have hstable : (prefixWord ++ tailWord_7976522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976522).length < 2 ^ (prefixWord ++ tailWord_7976522).sum := by decide
  have hdescent : baseEnd_7976522 < baseStart_7976522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976535 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_7976535 : Nat := 118140960795 + 7976535 * 2 ^ 59
def prefixEnd_7976535 : Nat := 4983230072969 + 3 ^ 40 * 7976535 * 2
def baseEnd_7976535 : Nat := 4095796412411054503829089

theorem tailTrace_7976535 : CollatzResearch.WordTrace tailWord_7976535 prefixEnd_7976535 4095796412411054503829089 := by
  unfold tailWord_7976535
  simp only [CollatzResearch.WordTrace]
  refine ⟨290928132157383453566163059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193952088104922302377442039 290928132157383453566163059)
  ·
    refine ⟨436392198236075180349244589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290928132157383453566163059 436392198236075180349244589)
    ·
      refine ⟨163647074338528192630966721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436392198236075180349244589 163647074338528192630966721)
      ·
        refine ⟨122735305753896144473225041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163647074338528192630966721 122735305753896144473225041)
        ·
          refine ⟨92051479315422108354918781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122735305753896144473225041 92051479315422108354918781)
          ·
            refine ⟨34519304743283290633094543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92051479315422108354918781 34519304743283290633094543)
            ·
              refine ⟨51778957114924935949641815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34519304743283290633094543 51778957114924935949641815)
              ·
                refine ⟨77668435672387403924462723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51778957114924935949641815 77668435672387403924462723)
                ·
                  refine ⟨116502653508581105886694085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77668435672387403924462723 116502653508581105886694085)
                  ·
                    refine ⟨21844247532858957353755141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116502653508581105886694085 21844247532858957353755141)
                    ·
                      refine ⟨4095796412411054503829089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21844247532858957353755141 4095796412411054503829089)
                      ·
                        rfl

theorem cell23_7976535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_7976535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976535 prefixEnd_7976535 := by exact prefixLift 7976535
  have htrace : WordTrace (prefixWord ++ tailWord_7976535) baseStart_7976535 baseEnd_7976535 := by
    simpa [prefixWord, tailWord_7976535, baseEnd_7976535] using wordTrace_append hprefix tailTrace_7976535
  have hstable : (prefixWord ++ tailWord_7976535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976535).length < 2 ^ (prefixWord ++ tailWord_7976535).sum := by decide
  have hdescent : baseEnd_7976535 < baseStart_7976535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976545 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 7]
def baseStart_7976545 : Nat := 118140960795 + 7976545 * 2 ^ 59
def prefixEnd_7976545 : Nat := 4983230072969 + 3 ^ 40 * 7976545 * 2
def baseEnd_7976545 : Nat := 455089060801955496078227

theorem tailTrace_7976545 : CollatzResearch.WordTrace tailWord_7976545 prefixEnd_7976545 455089060801955496078227 := by
  unfold tailWord_7976545
  simp only [CollatzResearch.WordTrace]
  refine ⟨290928496887347225274027089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193952331258231483516018059 290928496887347225274027089)
  ·
    refine ⟨218196372665510418955520317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290928496887347225274027089 218196372665510418955520317)
    ·
      refine ⟨81823639749566407108320119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218196372665510418955520317 81823639749566407108320119)
      ·
        refine ⟨122735459624349610662480179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81823639749566407108320119 122735459624349610662480179)
        ·
          refine ⟨184103189436524415993720269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122735459624349610662480179 184103189436524415993720269)
          ·
            refine ⟨69038696038696655997645101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184103189436524415993720269 69038696038696655997645101)
            ·
              refine ⟨25889511014511245999116913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69038696038696655997645101 25889511014511245999116913)
              ·
                refine ⟨19417133260883434499337685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25889511014511245999116913 19417133260883434499337685)
                ·
                  refine ⟨455089060801955496078227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19417133260883434499337685 455089060801955496078227)
                  ·
                    rfl

theorem cell23_7976545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 7].length) (baseStart_7976545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976545 prefixEnd_7976545 := by exact prefixLift 7976545
  have htrace : WordTrace (prefixWord ++ tailWord_7976545) baseStart_7976545 baseEnd_7976545 := by
    simpa [prefixWord, tailWord_7976545, baseEnd_7976545] using wordTrace_append hprefix tailTrace_7976545
  have hstable : (prefixWord ++ tailWord_7976545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976545).length < 2 ^ (prefixWord ++ tailWord_7976545).sum := by decide
  have hdescent : baseEnd_7976545 < baseStart_7976545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976573 : List Nat := [1, 4, 1, 1, 4, 3, 1, 2, 2, 2, 2]
def baseStart_7976573 : Nat := 118140960795 + 7976573 * 2 ^ 59
def prefixEnd_7976573 : Nat := 4983230072969 + 3 ^ 40 * 7976573 * 2
def baseEnd_7976573 : Nat := 4095815924675925355153915

theorem tailTrace_7976573 : CollatzResearch.WordTrace tailWord_7976573 prefixEnd_7976573 4095815924675925355153915 := by
  unfold tailWord_7976573
  simp only [CollatzResearch.WordTrace]
  refine ⟨290929518131245786056046373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193953012087497190704030915 290929518131245786056046373)
  ·
    refine ⟨54549284649608584885508695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290929518131245786056046373 54549284649608584885508695)
    ·
      refine ⟨81823926974412877328263043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54549284649608584885508695 81823926974412877328263043)
      ·
        refine ⟨122735890461619315992394565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81823926974412877328263043 122735890461619315992394565)
        ·
          refine ⟨23012979461553621748573981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122735890461619315992394565 23012979461553621748573981)
          ·
            refine ⟨8629867298082608155715243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23012979461553621748573981 8629867298082608155715243)
            ·
              refine ⟨12944800947123912233572865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8629867298082608155715243 12944800947123912233572865)
              ·
                refine ⟨9708600710342934175179649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12944800947123912233572865 9708600710342934175179649)
                ·
                  refine ⟨7281450532757200631384737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9708600710342934175179649 7281450532757200631384737)
                  ·
                    refine ⟨5461087899567900473538553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7281450532757200631384737 5461087899567900473538553)
                    ·
                      refine ⟨4095815924675925355153915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461087899567900473538553 4095815924675925355153915)
                      ·
                        rfl

theorem cell23_7976573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_7976573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976573 prefixEnd_7976573 := by exact prefixLift 7976573
  have htrace : WordTrace (prefixWord ++ tailWord_7976573) baseStart_7976573 baseEnd_7976573 := by
    simpa [prefixWord, tailWord_7976573, baseEnd_7976573] using wordTrace_append hprefix tailTrace_7976573
  have hstable : (prefixWord ++ tailWord_7976573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976573).length < 2 ^ (prefixWord ++ tailWord_7976573).sum := by decide
  have hdescent : baseEnd_7976573 < baseStart_7976573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976585 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 5]
def baseStart_7976585 : Nat := 118140960795 + 7976585 * 2 ^ 59
def prefixEnd_7976585 : Nat := 4983230072969 + 3 ^ 40 * 7976585 * 2
def baseEnd_7976585 : Nat := 4095822086443779308203859

theorem tailTrace_7976585 : CollatzResearch.WordTrace tailWord_7976585 prefixEnd_7976585 4095822086443779308203859 := by
  unfold tailWord_7976585
  simp only [CollatzResearch.WordTrace]
  refine ⟨290929955807202312105483209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193953303871468208070322139 290929955807202312105483209)
  ·
    refine ⟨218197466855401734079112407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290929955807202312105483209 218197466855401734079112407)
    ·
      refine ⟨327296200283102601118668611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218197466855401734079112407 327296200283102601118668611)
      ·
        refine ⟨490944300424653901678002917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327296200283102601118668611 490944300424653901678002917)
        ·
          refine ⟨92052056329622606564625547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490944300424653901678002917 92052056329622606564625547)
          ·
            refine ⟨138078084494433909846938321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92052056329622606564625547 138078084494433909846938321)
            ·
              refine ⟨103558563370825432385203741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138078084494433909846938321 103558563370825432385203741)
              ·
                refine ⟨38834461264059537144451403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103558563370825432385203741 38834461264059537144451403)
                ·
                  refine ⟨58251691896089305716677105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38834461264059537144451403 58251691896089305716677105)
                  ·
                    refine ⟨43688768922066979287507829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58251691896089305716677105 43688768922066979287507829)
                    ·
                      refine ⟨4095822086443779308203859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43688768922066979287507829 4095822086443779308203859)
                      ·
                        rfl

theorem cell23_7976585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_7976585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976585 prefixEnd_7976585 := by exact prefixLift 7976585
  have htrace : WordTrace (prefixWord ++ tailWord_7976585) baseStart_7976585 baseEnd_7976585 := by
    simpa [prefixWord, tailWord_7976585, baseEnd_7976585] using wordTrace_append hprefix tailTrace_7976585
  have hstable : (prefixWord ++ tailWord_7976585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976585).length < 2 ^ (prefixWord ++ tailWord_7976585).sum := by decide
  have hdescent : baseEnd_7976585 < baseStart_7976585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976605 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_7976605 : Nat := 118140960795 + 7976605 * 2 ^ 59
def prefixEnd_7976605 : Nat := 4983230072969 + 3 ^ 40 * 7976605 * 2
def baseEnd_7976605 : Nat := 1365277452018956409984589

theorem tailTrace_7976605 : CollatzResearch.WordTrace tailWord_7976605 prefixEnd_7976605 1365277452018956409984589 := by
  unfold tailWord_7976605
  simp only [CollatzResearch.WordTrace]
  refine ⟨290930685267129855521211269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193953790178086570347474179 290930685267129855521211269)
  ·
    refine ⟨54549503487586847910227113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290930685267129855521211269 54549503487586847910227113)
    ·
      refine ⟨40912127615690135932670335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54549503487586847910227113 40912127615690135932670335)
      ·
        refine ⟨61368191423535203899005503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40912127615690135932670335 61368191423535203899005503)
        ·
          refine ⟨92052287135302805848508255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61368191423535203899005503 92052287135302805848508255)
          ·
            refine ⟨138078430702954208772762383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92052287135302805848508255 138078430702954208772762383)
            ·
              refine ⟨207117646054431313159143575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138078430702954208772762383 207117646054431313159143575)
              ·
                refine ⟨310676469081646969738715363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207117646054431313159143575 310676469081646969738715363)
                ·
                  refine ⟨466014703622470454608073045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310676469081646969738715363 466014703622470454608073045)
                  ·
                    refine ⟨1365277452018956409984589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 466014703622470454608073045 1365277452018956409984589)
                    ·
                      rfl

theorem cell23_7976605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_7976605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976605 prefixEnd_7976605 := by exact prefixLift 7976605
  have htrace : WordTrace (prefixWord ++ tailWord_7976605) baseStart_7976605 baseEnd_7976605 := by
    simpa [prefixWord, tailWord_7976605, baseEnd_7976605] using wordTrace_append hprefix tailTrace_7976605
  have hstable : (prefixWord ++ tailWord_7976605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976605).length < 2 ^ (prefixWord ++ tailWord_7976605).sum := by decide
  have hdescent : baseEnd_7976605 < baseStart_7976605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976612 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_7976612 : Nat := 118140960795 + 7976612 * 2 ^ 59
def prefixEnd_7976612 : Nat := 4983230072969 + 3 ^ 40 * 7976612 * 2
def baseEnd_7976612 : Nat := 4095835950421450702566235

theorem tailTrace_7976612 : CollatzResearch.WordTrace tailWord_7976612 prefixEnd_7976612 4095835950421450702566235 := by
  unfold tailWord_7976612
  simp only [CollatzResearch.WordTrace]
  refine ⟨145465470289052247858358045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193953960385402997144477393 145465470289052247858358045)
  ·
    refine ⟨54549551358394592946884267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145465470289052247858358045 54549551358394592946884267)
    ·
      refine ⟨81824327037591889420326401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54549551358394592946884267 81824327037591889420326401)
      ·
        refine ⟨61368245278193917065244801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81824327037591889420326401 61368245278193917065244801)
        ·
          refine ⟨46026183958645437798933601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61368245278193917065244801 46026183958645437798933601)
          ·
            refine ⟨34519637968984078349200201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46026183958645437798933601 34519637968984078349200201)
            ·
              refine ⟨25889728476738058761900151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34519637968984078349200201 25889728476738058761900151)
              ·
                refine ⟨38834592715107088142850227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25889728476738058761900151 38834592715107088142850227)
                ·
                  refine ⟨58251889072660632214275341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38834592715107088142850227 58251889072660632214275341)
                  ·
                    refine ⟨21844458402247737080353253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58251889072660632214275341 21844458402247737080353253)
                    ·
                      refine ⟨4095835950421450702566235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21844458402247737080353253 4095835950421450702566235)
                      ·
                        rfl

theorem cell23_7976612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_7976612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976612 prefixEnd_7976612 := by exact prefixLift 7976612
  have htrace : WordTrace (prefixWord ++ tailWord_7976612) baseStart_7976612 baseEnd_7976612 := by
    simpa [prefixWord, tailWord_7976612, baseEnd_7976612] using wordTrace_append hprefix tailTrace_7976612
  have hstable : (prefixWord ++ tailWord_7976612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976612).length < 2 ^ (prefixWord ++ tailWord_7976612).sum := by decide
  have hdescent : baseEnd_7976612 < baseStart_7976612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976655 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 6]
def baseStart_7976655 : Nat := 118140960795 + 7976655 * 2 ^ 59
def prefixEnd_7976655 : Nat := 4983230072969 + 3 ^ 40 * 7976655 * 2
def baseEnd_7976655 : Nat := 4095858030089594034328537

theorem tailTrace_7976655 : CollatzResearch.WordTrace tailWord_7976655 prefixEnd_7976655 4095858030089594034328537 := by
  unfold tailWord_7976655
  simp only [CollatzResearch.WordTrace]
  refine ⟨290932508916948714060531419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193955005944632476040354279 290932508916948714060531419)
  ·
    refine ⟨436398763375423071090797129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290932508916948714060531419 436398763375423071090797129)
    ·
      refine ⟨327299072531567303318097847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436398763375423071090797129 327299072531567303318097847)
      ·
        refine ⟨490948608797350954977146771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327299072531567303318097847 490948608797350954977146771)
        ·
          refine ⟨736422913196026432465720157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490948608797350954977146771 736422913196026432465720157)
          ·
            refine ⟨276158592448509912174645059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736422913196026432465720157 276158592448509912174645059)
            ·
              refine ⟨414237888672764868261967589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276158592448509912174645059 414237888672764868261967589)
              ·
                refine ⟨77669604126143412799118923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 414237888672764868261967589 77669604126143412799118923)
                ·
                  refine ⟨116504406189215119198678385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77669604126143412799118923 116504406189215119198678385)
                  ·
                    refine ⟨87378304641911339399008789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116504406189215119198678385 87378304641911339399008789)
                    ·
                      refine ⟨4095858030089594034328537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87378304641911339399008789 4095858030089594034328537)
                      ·
                        rfl

theorem cell23_7976655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_7976655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976655 prefixEnd_7976655 := by exact prefixLift 7976655
  have htrace : WordTrace (prefixWord ++ tailWord_7976655) baseStart_7976655 baseEnd_7976655 := by
    simpa [prefixWord, tailWord_7976655, baseEnd_7976655] using wordTrace_append hprefix tailTrace_7976655
  have hstable : (prefixWord ++ tailWord_7976655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976655).length < 2 ^ (prefixWord ++ tailWord_7976655).sum := by decide
  have hdescent : baseEnd_7976655 < baseStart_7976655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976706 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_7976706 : Nat := 118140960795 + 7976706 * 2 ^ 59
def prefixEnd_7976706 : Nat := 4983230072969 + 3 ^ 40 * 7976706 * 2
def baseEnd_7976706 : Nat := 4095884217602973334790803

theorem tailTrace_7976706 : CollatzResearch.WordTrace tailWord_7976706 prefixEnd_7976706 4095884217602973334790803 := by
  unfold tailWord_7976706
  simp only [CollatzResearch.WordTrace]
  refine ⟨72733592259940987442659493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193956246026509299847091981 72733592259940987442659493)
  ·
    refine ⟨13637548548738935145498655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72733592259940987442659493 13637548548738935145498655)
    ·
      refine ⟨20456322823108402718247983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13637548548738935145498655 20456322823108402718247983)
      ·
        refine ⟨30684484234662604077371975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20456322823108402718247983 30684484234662604077371975)
        ·
          refine ⟨46026726351993906116057963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30684484234662604077371975 46026726351993906116057963)
          ·
            refine ⟨69040089527990859174086945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46026726351993906116057963 69040089527990859174086945)
            ·
              refine ⟨51780067145993144380565209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69040089527990859174086945 51780067145993144380565209)
              ·
                refine ⟨38835050359494858285423907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51780067145993144380565209 38835050359494858285423907)
                ·
                  refine ⟨58252575539242287428135861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38835050359494858285423907 58252575539242287428135861)
                  ·
                    refine ⟨5461178956803964446387737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58252575539242287428135861 5461178956803964446387737)
                    ·
                      refine ⟨4095884217602973334790803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461178956803964446387737 4095884217602973334790803)
                      ·
                        rfl

theorem cell23_7976706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_7976706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976706 prefixEnd_7976706 := by exact prefixLift 7976706
  have htrace : WordTrace (prefixWord ++ tailWord_7976706) baseStart_7976706 baseEnd_7976706 := by
    simpa [prefixWord, tailWord_7976706, baseEnd_7976706] using wordTrace_append hprefix tailTrace_7976706
  have hstable : (prefixWord ++ tailWord_7976706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976706).length < 2 ^ (prefixWord ++ tailWord_7976706).sum := by decide
  have hdescent : baseEnd_7976706 < baseStart_7976706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976736 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 5, 2, 2]
def baseStart_7976736 : Nat := 118140960795 + 7976736 * 2 ^ 59
def prefixEnd_7976736 : Nat := 4983230072969 + 3 ^ 40 * 7976736 * 2
def baseEnd_7976736 : Nat := 4095899622022608217415665

theorem tailTrace_7976736 : CollatzResearch.WordTrace tailWord_7976736 prefixEnd_7976736 4095899622022608217415665 := by
  unfold tailWord_7976736
  simp only [CollatzResearch.WordTrace]
  refine ⟨145467731614827632447115031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193956975486436843262820041 145467731614827632447115031)
  ·
    refine ⟨218201597422241448670672547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145467731614827632447115031 218201597422241448670672547)
    ·
      refine ⟨327302396133362173006008821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218201597422241448670672547 327302396133362173006008821)
      ·
        refine ⟨30684599637502703719313327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 327302396133362173006008821 30684599637502703719313327)
        ·
          refine ⟨46026899456254055578969991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30684599637502703719313327 46026899456254055578969991)
          ·
            refine ⟨69040349184381083368454987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46026899456254055578969991 69040349184381083368454987)
            ·
              refine ⟨103560523776571625052682481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69040349184381083368454987 103560523776571625052682481)
              ·
                refine ⟨77670392832428718789511861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103560523776571625052682481 77670392832428718789511861)
                ·
                  refine ⟨7281599328040192386516737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77670392832428718789511861 7281599328040192386516737)
                  ·
                    refine ⟨5461199496030144289887553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7281599328040192386516737 5461199496030144289887553)
                    ·
                      refine ⟨4095899622022608217415665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461199496030144289887553 4095899622022608217415665)
                      ·
                        rfl

theorem cell23_7976736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_7976736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976736 prefixEnd_7976736 := by exact prefixLift 7976736
  have htrace : WordTrace (prefixWord ++ tailWord_7976736) baseStart_7976736 baseEnd_7976736 := by
    simpa [prefixWord, tailWord_7976736, baseEnd_7976736] using wordTrace_append hprefix tailTrace_7976736
  have hstable : (prefixWord ++ tailWord_7976736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976736).length < 2 ^ (prefixWord ++ tailWord_7976736).sum := by decide
  have hdescent : baseEnd_7976736 < baseStart_7976736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976752 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 3]
def baseStart_7976752 : Nat := 118140960795 + 7976752 * 2 ^ 59
def prefixEnd_7976752 : Nat := 4983230072969 + 3 ^ 40 * 7976752 * 2
def baseEnd_7976752 : Nat := 4095907837713080154815591

theorem tailTrace_7976752 : CollatzResearch.WordTrace tailWord_7976752 prefixEnd_7976752 4095907837713080154815591 := by
  unfold tailWord_7976752
  simp only [CollatzResearch.WordTrace]
  refine ⟨145468023398798649813406255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193957364531731533084541673 145468023398798649813406255)
  ·
    refine ⟨218202035098197974720109383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145468023398798649813406255 218202035098197974720109383)
    ·
      refine ⟨327303052647296962080164075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218202035098197974720109383 327303052647296962080164075)
      ·
        refine ⟨490954578970945443120246113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327303052647296962080164075 490954578970945443120246113)
        ·
          refine ⟨368215934228209082340184585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490954578970945443120246113 368215934228209082340184585)
          ·
            refine ⟨276161950671156811755138439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368215934228209082340184585 276161950671156811755138439)
            ·
              refine ⟨414242926006735217632707659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276161950671156811755138439 414242926006735217632707659)
              ·
                refine ⟨621364389010102826449061489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414242926006735217632707659 621364389010102826449061489)
                ·
                  refine ⟨466023291757577119836796117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621364389010102826449061489 466023291757577119836796117)
                  ·
                    refine ⟨10922420900568213746174909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 466023291757577119836796117 10922420900568213746174909)
                    ·
                      refine ⟨4095907837713080154815591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10922420900568213746174909 4095907837713080154815591)
                      ·
                        rfl

theorem cell23_7976752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 3].length) (baseStart_7976752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976752 prefixEnd_7976752 := by exact prefixLift 7976752
  have htrace : WordTrace (prefixWord ++ tailWord_7976752) baseStart_7976752 baseEnd_7976752 := by
    simpa [prefixWord, tailWord_7976752, baseEnd_7976752] using wordTrace_append hprefix tailTrace_7976752
  have hstable : (prefixWord ++ tailWord_7976752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976752).length < 2 ^ (prefixWord ++ tailWord_7976752).sum := by decide
  have hdescent : baseEnd_7976752 < baseStart_7976752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976753 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 3, 2, 2]
def baseStart_7976753 : Nat := 118140960795 + 7976753 * 2 ^ 59
def prefixEnd_7976753 : Nat := 4983230072969 + 3 ^ 40 * 7976753 * 2
def baseEnd_7976753 : Nat := 4095908351193734650903087

theorem tailTrace_7976753 : CollatzResearch.WordTrace tailWord_7976753 prefixEnd_7976753 4095908351193734650903087 := by
  unfold tailWord_7976753
  simp only [CollatzResearch.WordTrace]
  refine ⟨290936083270593676797598913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193957388847062451198399275 290936083270593676797598913)
  ·
    refine ⟨218202062452945257598199185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290936083270593676797598913 218202062452945257598199185)
    ·
      refine ⟨163651546839708943198649389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218202062452945257598199185 163651546839708943198649389)
      ·
        refine ⟨61369330064890853699493521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163651546839708943198649389 61369330064890853699493521)
        ·
          refine ⟨46026997548668140274620141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61369330064890853699493521 46026997548668140274620141)
          ·
            refine ⟨17260124080750552602982553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46026997548668140274620141 17260124080750552602982553)
            ·
              refine ⟨12945093060562914452236915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17260124080750552602982553 12945093060562914452236915)
              ·
                refine ⟨19417639590844371678355373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12945093060562914452236915 19417639590844371678355373)
                ·
                  refine ⟨7281614846566639379383265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19417639590844371678355373 7281614846566639379383265)
                  ·
                    refine ⟨5461211134924979534537449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7281614846566639379383265 5461211134924979534537449)
                    ·
                      refine ⟨4095908351193734650903087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461211134924979534537449 4095908351193734650903087)
                      ·
                        rfl

theorem cell23_7976753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_7976753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976753 prefixEnd_7976753 := by exact prefixLift 7976753
  have htrace : WordTrace (prefixWord ++ tailWord_7976753) baseStart_7976753 baseEnd_7976753 := by
    simpa [prefixWord, tailWord_7976753, baseEnd_7976753] using wordTrace_append hprefix tailTrace_7976753
  have hstable : (prefixWord ++ tailWord_7976753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976753).length < 2 ^ (prefixWord ++ tailWord_7976753).sum := by decide
  have hdescent : baseEnd_7976753 < baseStart_7976753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976756 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_7976756 : Nat := 118140960795 + 7976756 * 2 ^ 59
def prefixEnd_7976756 : Nat := 4983230072969 + 3 ^ 40 * 7976756 * 2
def baseEnd_7976756 : Nat := 4095909891635698139165573

theorem tailTrace_7976756 : CollatzResearch.WordTrace tailWord_7976756 prefixEnd_7976756 4095909891635698139165573 := by
  unfold tailWord_7976756
  simp only [CollatzResearch.WordTrace]
  refine ⟨145468096344791404154979061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193957461793055205539972081 145468096344791404154979061)
  ·
    refine ⟨13637634032324194139529287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145468096344791404154979061 13637634032324194139529287)
    ·
      refine ⟨20456451048486291209293931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13637634032324194139529287 20456451048486291209293931)
      ·
        refine ⟨30684676572729436813940897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20456451048486291209293931 30684676572729436813940897)
        ·
          refine ⟨23013507429547077610455673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30684676572729436813940897 23013507429547077610455673)
          ·
            refine ⟨17260130572160308207841755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23013507429547077610455673 17260130572160308207841755)
            ·
              refine ⟨25890195858240462311762633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17260130572160308207841755 25890195858240462311762633)
              ·
                refine ⟨19417646893680346733821975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25890195858240462311762633 19417646893680346733821975)
                ·
                  refine ⟨29126470340520520100732963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19417646893680346733821975 29126470340520520100732963)
                  ·
                    refine ⟨43689705510780780151099445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29126470340520520100732963 43689705510780780151099445)
                    ·
                      refine ⟨4095909891635698139165573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43689705510780780151099445 4095909891635698139165573)
                      ·
                        rfl

theorem cell23_7976756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_7976756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976756 prefixEnd_7976756 := by exact prefixLift 7976756
  have htrace : WordTrace (prefixWord ++ tailWord_7976756) baseStart_7976756 baseEnd_7976756 := by
    simpa [prefixWord, tailWord_7976756, baseEnd_7976756] using wordTrace_append hprefix tailTrace_7976756
  have hstable : (prefixWord ++ tailWord_7976756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976756).length < 2 ^ (prefixWord ++ tailWord_7976756).sum := by decide
  have hdescent : baseEnd_7976756 < baseStart_7976756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976766 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_7976766 : Nat := 118140960795 + 7976766 * 2 ^ 59
def prefixEnd_7976766 : Nat := 4983230072969 + 3 ^ 40 * 7976766 * 2
def baseEnd_7976766 : Nat := 4095915026442243100040527

theorem tailTrace_7976766 : CollatzResearch.WordTrace tailWord_7976766 prefixEnd_7976766 4095915026442243100040527 := by
  unfold tailWord_7976766
  simp only [CollatzResearch.WordTrace]
  refine ⟨36367069677443322502227769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193957704946364386678548101 36367069677443322502227769)
  ·
    refine ⟨27275302258082491876670827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36367069677443322502227769 27275302258082491876670827)
    ·
      refine ⟨40912953387123737815006241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27275302258082491876670827 40912953387123737815006241)
      ·
        refine ⟨30684715040342803361254681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40912953387123737815006241 30684715040342803361254681)
        ·
          refine ⟨23013536280257102520941011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30684715040342803361254681 23013536280257102520941011)
          ·
            refine ⟨34520304420385653781411517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23013536280257102520941011 34520304420385653781411517)
            ·
              refine ⟨12945114157644620168029319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34520304420385653781411517 12945114157644620168029319)
              ·
                refine ⟨19417671236466930252043979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12945114157644620168029319 19417671236466930252043979)
                ·
                  refine ⟨29126506854700395378065969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19417671236466930252043979 29126506854700395378065969)
                  ·
                    refine ⟨21844880141025296533549477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29126506854700395378065969 21844880141025296533549477)
                    ·
                      refine ⟨4095915026442243100040527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21844880141025296533549477 4095915026442243100040527)
                      ·
                        rfl

theorem cell23_7976766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_7976766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976766 prefixEnd_7976766 := by exact prefixLift 7976766
  have htrace : WordTrace (prefixWord ++ tailWord_7976766) baseStart_7976766 baseEnd_7976766 := by
    simpa [prefixWord, tailWord_7976766, baseEnd_7976766] using wordTrace_append hprefix tailTrace_7976766
  have hstable : (prefixWord ++ tailWord_7976766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976766).length < 2 ^ (prefixWord ++ tailWord_7976766).sum := by decide
  have hdescent : baseEnd_7976766 < baseStart_7976766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976786 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_7976786 : Nat := 118140960795 + 7976786 * 2 ^ 59
def prefixEnd_7976786 : Nat := 4983230072969 + 3 ^ 40 * 7976786 * 2
def baseEnd_7976786 : Nat := 4095925296055333021790435

theorem tailTrace_7976786 : CollatzResearch.WordTrace tailWord_7976786 prefixEnd_7976786 4095925296055333021790435 := by
  unfold tailWord_7976786
  simp only [CollatzResearch.WordTrace]
  refine ⟨72734321719868530858387553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193958191252982748955700141 72734321719868530858387553)
  ·
    refine ⟨54550741289901398143790665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72734321719868530858387553 54550741289901398143790665)
    ·
      refine ⟨40913055967426048607842999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54550741289901398143790665 40913055967426048607842999)
      ·
        refine ⟨61369583951139072911764499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40913055967426048607842999 61369583951139072911764499)
        ·
          refine ⟨92054375926708609367646749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61369583951139072911764499 92054375926708609367646749)
          ·
            refine ⟨34520390972515728512867531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92054375926708609367646749 34520390972515728512867531)
            ·
              refine ⟨51780586458773592769301297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34520390972515728512867531 51780586458773592769301297)
              ·
                refine ⟨38835439844080194576975973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51780586458773592769301297 38835439844080194576975973)
                ·
                  refine ⟨7281644970765036483182995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38835439844080194576975973 7281644970765036483182995)
                  ·
                    refine ⟨10922467456147554724774493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7281644970765036483182995 10922467456147554724774493)
                    ·
                      refine ⟨4095925296055333021790435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10922467456147554724774493 4095925296055333021790435)
                      ·
                        rfl

theorem cell23_7976786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_7976786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976786 prefixEnd_7976786 := by exact prefixLift 7976786
  have htrace : WordTrace (prefixWord ++ tailWord_7976786) baseStart_7976786 baseEnd_7976786 := by
    simpa [prefixWord, tailWord_7976786, baseEnd_7976786] using wordTrace_append hprefix tailTrace_7976786
  have hstable : (prefixWord ++ tailWord_7976786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976786).length < 2 ^ (prefixWord ++ tailWord_7976786).sum := by decide
  have hdescent : baseEnd_7976786 < baseStart_7976786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976792 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_7976792 : Nat := 118140960795 + 7976792 * 2 ^ 59
def prefixEnd_7976792 : Nat := 4983230072969 + 3 ^ 40 * 7976792 * 2
def baseEnd_7976792 : Nat := 4095928376939259998315407

theorem tailTrace_7976792 : CollatzResearch.WordTrace tailWord_7976792 prefixEnd_7976792 4095928376939259998315407 := by
  unfold tailWord_7976792
  simp only [CollatzResearch.WordTrace]
  refine ⟨145468752858726193229134315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193958337144968257638845753 145468752858726193229134315)
  ·
    refine ⟨218203129288089289843701473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145468752858726193229134315 218203129288089289843701473)
    ·
      refine ⟨163652346966066967382776105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218203129288089289843701473 163652346966066967382776105)
      ·
        refine ⟨122739260224550225537082079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163652346966066967382776105 122739260224550225537082079)
        ·
          refine ⟨184108890336825338305623119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122739260224550225537082079 184108890336825338305623119)
          ·
            refine ⟨276163335505238007458434679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184108890336825338305623119 276163335505238007458434679)
            ·
              refine ⟨414245003257857011187652019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276163335505238007458434679 414245003257857011187652019)
              ·
                refine ⟨621367504886785516781478029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414245003257857011187652019 621367504886785516781478029)
                ·
                  refine ⟨233012814332544568793054261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 621367504886785516781478029 233012814332544568793054261)
                  ·
                    refine ⟨21844951343676053324348837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 233012814332544568793054261 21844951343676053324348837)
                    ·
                      refine ⟨4095928376939259998315407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21844951343676053324348837 4095928376939259998315407)
                      ·
                        rfl

theorem cell23_7976792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_7976792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976792 prefixEnd_7976792 := by exact prefixLift 7976792
  have htrace : WordTrace (prefixWord ++ tailWord_7976792) baseStart_7976792 baseEnd_7976792 := by
    simpa [prefixWord, tailWord_7976792, baseEnd_7976792] using wordTrace_append hprefix tailTrace_7976792
  have hstable : (prefixWord ++ tailWord_7976792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976792).length < 2 ^ (prefixWord ++ tailWord_7976792).sum := by decide
  have hdescent : baseEnd_7976792 < baseStart_7976792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976830 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_7976830 : Nat := 118140960795 + 7976830 * 2 ^ 59
def prefixEnd_7976830 : Nat := 4983230072969 + 3 ^ 40 * 7976830 * 2
def baseEnd_7976830 : Nat := 4095947889204130849640233

theorem tailTrace_7976830 : CollatzResearch.WordTrace tailWord_7976830 prefixEnd_7976830 4095947889204130849640233 := by
  unfold tailWord_7976830
  simp only [CollatzResearch.WordTrace]
  refine ⟨36367361461414339868518993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193959261127543145965434629 36367361461414339868518993)
  ·
    refine ⟨27275521096060754901389245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36367361461414339868518993 27275521096060754901389245)
    ·
      refine ⟨10228320411022783088020967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27275521096060754901389245 10228320411022783088020967)
      ·
        refine ⟨15342480616534174632031451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10228320411022783088020967 15342480616534174632031451)
        ·
          refine ⟨23013720924801261948047177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15342480616534174632031451 23013720924801261948047177)
          ·
            refine ⟨17260290693600946461035383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23013720924801261948047177 17260290693600946461035383)
            ·
              refine ⟨25890436040401419691553075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17260290693600946461035383 25890436040401419691553075)
              ·
                refine ⟨38835654060602129537329613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25890436040401419691553075 38835654060602129537329613)
                ·
                  refine ⟨14563370272725798576498605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38835654060602129537329613 14563370272725798576498605)
                  ·
                    refine ⟨5461263852272174466186977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14563370272725798576498605 5461263852272174466186977)
                    ·
                      refine ⟨4095947889204130849640233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461263852272174466186977 4095947889204130849640233)
                      ·
                        rfl

theorem cell23_7976830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_7976830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976830 prefixEnd_7976830 := by exact prefixLift 7976830
  have htrace : WordTrace (prefixWord ++ tailWord_7976830) baseStart_7976830 baseEnd_7976830 := by
    simpa [prefixWord, tailWord_7976830, baseEnd_7976830] using wordTrace_append hprefix tailTrace_7976830
  have hstable : (prefixWord ++ tailWord_7976830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976830).length < 2 ^ (prefixWord ++ tailWord_7976830).sum := by decide
  have hdescent : baseEnd_7976830 < baseStart_7976830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976832 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 9]
def baseStart_7976832 : Nat := 118140960795 + 7976832 * 2 ^ 59
def prefixEnd_7976832 : Nat := 4983230072969 + 3 ^ 40 * 7976832 * 2
def baseEnd_7976832 : Nat := 455105435129493315757247

theorem tailTrace_7976832 : CollatzResearch.WordTrace tailWord_7976832 prefixEnd_7976832 455105435129493315757247 := by
  unfold tailWord_7976832
  simp only [CollatzResearch.WordTrace]
  refine ⟨145469482318653736644862375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193959309758204982193149833 145469482318653736644862375)
  ·
    refine ⟨218204223477980604967293563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145469482318653736644862375 218204223477980604967293563)
    ·
      refine ⟨327306335216970907450940345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218204223477980604967293563 327306335216970907450940345)
      ·
        refine ⟨245479751412728180588205259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327306335216970907450940345 245479751412728180588205259)
        ·
          refine ⟨368219627119092270882307889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245479751412728180588205259 368219627119092270882307889)
          ·
            refine ⟨276164720339319203161730917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368219627119092270882307889 276164720339319203161730917)
            ·
              refine ⟨51780885063622350592824547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276164720339319203161730917 51780885063622350592824547)
              ·
                refine ⟨77671327595433525889236821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51780885063622350592824547 77671327595433525889236821)
                ·
                  refine ⟨455105435129493315757247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77671327595433525889236821 455105435129493315757247)
                  ·
                    rfl

theorem cell23_7976832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 9].length) (baseStart_7976832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976832 prefixEnd_7976832 := by exact prefixLift 7976832
  have htrace : WordTrace (prefixWord ++ tailWord_7976832) baseStart_7976832 baseEnd_7976832 := by
    simpa [prefixWord, tailWord_7976832, baseEnd_7976832] using wordTrace_append hprefix tailTrace_7976832
  have hstable : (prefixWord ++ tailWord_7976832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976832).length < 2 ^ (prefixWord ++ tailWord_7976832).sum := by decide
  have hdescent : baseEnd_7976832 < baseStart_7976832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976854 : List Nat := [5, 3, 1, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_7976854 : Nat := 118140960795 + 7976854 * 2 ^ 59
def prefixEnd_7976854 : Nat := 4983230072969 + 3 ^ 40 * 7976854 * 2
def baseEnd_7976854 : Nat := 4095960212739838755740123

theorem tailTrace_7976854 : CollatzResearch.WordTrace tailWord_7976854 prefixEnd_7976854 4095960212739838755740123 := by
  unfold tailWord_7976854
  simp only [CollatzResearch.WordTrace]
  refine ⟨18183735440201735690439101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193959844695485180698017077 18183735440201735690439101)
  ·
    refine ⟨6818900790075650883914663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18183735440201735690439101 6818900790075650883914663)
    ·
      refine ⟨10228351185113476325871995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6818900790075650883914663 10228351185113476325871995)
      ·
        refine ⟨15342526777670214488807993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10228351185113476325871995 15342526777670214488807993)
        ·
          refine ⟨11506895083252660866605995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15342526777670214488807993 11506895083252660866605995)
          ·
            refine ⟨17260342624878991299908993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11506895083252660866605995 17260342624878991299908993)
            ·
              refine ⟨12945256968659243474931745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17260342624878991299908993 12945256968659243474931745)
              ·
                refine ⟨9708942726494432606198809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12945256968659243474931745 9708942726494432606198809)
                ·
                  refine ⟨7281707044870824454649107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9708942726494432606198809 7281707044870824454649107)
                  ·
                    refine ⟨10922560567306236681973661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7281707044870824454649107 10922560567306236681973661)
                    ·
                      refine ⟨4095960212739838755740123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10922560567306236681973661 4095960212739838755740123)
                      ·
                        rfl

theorem cell23_7976854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_7976854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976854 prefixEnd_7976854 := by exact prefixLift 7976854
  have htrace : WordTrace (prefixWord ++ tailWord_7976854) baseStart_7976854 baseEnd_7976854 := by
    simpa [prefixWord, tailWord_7976854, baseEnd_7976854] using wordTrace_append hprefix tailTrace_7976854
  have hstable : (prefixWord ++ tailWord_7976854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976854).length < 2 ^ (prefixWord ++ tailWord_7976854).sum := by decide
  have hdescent : baseEnd_7976854 < baseStart_7976854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976860 : List Nat := [2, 2, 3, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_7976860 : Nat := 118140960795 + 7976860 * 2 ^ 59
def prefixEnd_7976860 : Nat := 4983230072969 + 3 ^ 40 * 7976860 * 2
def baseEnd_7976860 : Nat := 4095963293623765732265095

theorem tailTrace_7976860 : CollatzResearch.WordTrace tailWord_7976860 prefixEnd_7976860 4095963293623765732265095 := by
  unfold tailWord_7976860
  simp only [CollatzResearch.WordTrace]
  refine ⟨145469992940603017035872017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193959990587470689381162689 145469992940603017035872017)
  ·
    refine ⟨109102494705452262776904013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145469992940603017035872017 109102494705452262776904013)
    ·
      refine ⟨40913435514544598541339005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109102494705452262776904013 40913435514544598541339005)
      ·
        refine ⟨15342538317954224453002127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40913435514544598541339005 15342538317954224453002127)
        ·
          refine ⟨23013807476931336679503191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15342538317954224453002127 23013807476931336679503191)
          ·
            refine ⟨34520711215397005019254787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23013807476931336679503191 34520711215397005019254787)
            ·
              refine ⟨51781066823095507528882181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34520711215397005019254787 51781066823095507528882181)
              ·
                refine ⟨9708950029330407661665409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51781066823095507528882181 9708950029330407661665409)
                ·
                  refine ⟨7281712521997805746249057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9708950029330407661665409 7281712521997805746249057)
                  ·
                    refine ⟨5461284391498354309686793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7281712521997805746249057 5461284391498354309686793)
                    ·
                      refine ⟨4095963293623765732265095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461284391498354309686793 4095963293623765732265095)
                      ·
                        rfl

theorem cell23_7976860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_7976860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976860 prefixEnd_7976860 := by exact prefixLift 7976860
  have htrace : WordTrace (prefixWord ++ tailWord_7976860) baseStart_7976860 baseEnd_7976860 := by
    simpa [prefixWord, tailWord_7976860, baseEnd_7976860] using wordTrace_append hprefix tailTrace_7976860
  have hstable : (prefixWord ++ tailWord_7976860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976860).length < 2 ^ (prefixWord ++ tailWord_7976860).sum := by decide
  have hdescent : baseEnd_7976860 < baseStart_7976860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976916 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_7976916 : Nat := 118140960795 + 7976916 * 2 ^ 59
def prefixEnd_7976916 : Nat := 4983230072969 + 3 ^ 40 * 7976916 * 2
def baseEnd_7976916 : Nat := 4095992048540417513164837

theorem tailTrace_7976916 : CollatzResearch.WordTrace tailWord_7976916 prefixEnd_7976916 4095992048540417513164837 := by
  unfold tailWord_7976916
  simp only [CollatzResearch.WordTrace]
  refine ⟨145471014184501577817891301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193961352246002103757188401 145471014184501577817891301)
  ·
    refine ⟨27275815159594045840854619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145471014184501577817891301 27275815159594045840854619)
    ·
      refine ⟨40913722739391068761281929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27275815159594045840854619 40913722739391068761281929)
      ·
        refine ⟨30685292054543301570961447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40913722739391068761281929 30685292054543301570961447)
        ·
          refine ⟨46027938081814952356442171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30685292054543301570961447 46027938081814952356442171)
          ·
            refine ⟨69041907122722428534663257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46027938081814952356442171 69041907122722428534663257)
            ·
              refine ⟨51781430342041821400997443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69041907122722428534663257 51781430342041821400997443)
              ·
                refine ⟨77672145513062732101496165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51781430342041821400997443 77672145513062732101496165)
                ·
                  refine ⟨14563527283699262269030531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77672145513062732101496165 14563527283699262269030531)
                  ·
                    refine ⟨21845290925548893403545797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14563527283699262269030531 21845290925548893403545797)
                    ·
                      refine ⟨4095992048540417513164837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21845290925548893403545797 4095992048540417513164837)
                      ·
                        rfl

theorem cell23_7976916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_7976916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976916 prefixEnd_7976916 := by exact prefixLift 7976916
  have htrace : WordTrace (prefixWord ++ tailWord_7976916) baseStart_7976916 baseEnd_7976916 := by
    simpa [prefixWord, tailWord_7976916, baseEnd_7976916] using wordTrace_append hprefix tailTrace_7976916
  have hstable : (prefixWord ++ tailWord_7976916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976916).length < 2 ^ (prefixWord ++ tailWord_7976916).sum := by decide
  have hdescent : baseEnd_7976916 < baseStart_7976916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976939 : List Nat := [1, 1, 1, 1, 2, 3, 1, 7, 6]
def baseStart_7976939 : Nat := 118140960795 + 7976939 * 2 ^ 59
def prefixEnd_7976939 : Nat := 4983230072969 + 3 ^ 40 * 7976939 * 2
def baseEnd_7976939 : Nat := 455111539843941213686359

theorem tailTrace_7976939 : CollatzResearch.WordTrace tailWord_7976939 prefixEnd_7976939 455111539843941213686359 := by
  unfold tailWord_7976939
  simp only [CollatzResearch.WordTrace]
  refine ⟨290942867247919830563869871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193961911498613220375913247 290942867247919830563869871)
  ·
    refine ⟨436414300871879745845804807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290942867247919830563869871 436414300871879745845804807)
    ·
      refine ⟨654621451307819618768707211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436414300871879745845804807 654621451307819618768707211)
      ·
        refine ⟨981932176961729428153060817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654621451307819618768707211 981932176961729428153060817)
        ·
          refine ⟨736449132721297071114795613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981932176961729428153060817 736449132721297071114795613)
          ·
            refine ⟨276168424770486401668048355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736449132721297071114795613 276168424770486401668048355)
            ·
              refine ⟨414252637155729602502072533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276168424770486401668048355 414252637155729602502072533)
              ·
                refine ⟨9709046183337412558642325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 414252637155729602502072533 9709046183337412558642325)
                ·
                  refine ⟨455111539843941213686359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9709046183337412558642325 455111539843941213686359)
                  ·
                    rfl

theorem cell23_7976939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 6].length) (baseStart_7976939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976939 prefixEnd_7976939 := by exact prefixLift 7976939
  have htrace : WordTrace (prefixWord ++ tailWord_7976939) baseStart_7976939 baseEnd_7976939 := by
    simpa [prefixWord, tailWord_7976939, baseEnd_7976939] using wordTrace_append hprefix tailTrace_7976939
  have hstable : (prefixWord ++ tailWord_7976939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976939).length < 2 ^ (prefixWord ++ tailWord_7976939).sum := by decide
  have hdescent : baseEnd_7976939 < baseStart_7976939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976969 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 7, 5]
def baseStart_7976969 : Nat := 118140960795 + 7976969 * 2 ^ 59
def prefixEnd_7976969 : Nat := 4983230072969 + 3 ^ 40 * 7976969 * 2
def baseEnd_7976969 : Nat := 1365339754338368601934031

theorem tailTrace_7976969 : CollatzResearch.WordTrace tailWord_7976969 prefixEnd_7976969 1365339754338368601934031 := by
  unfold tailWord_7976969
  simp only [CollatzResearch.WordTrace]
  refine ⟨290943961437811145687461961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193962640958540763791641307 290943961437811145687461961)
  ·
    refine ⟨218207971078358359265596471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290943961437811145687461961 218207971078358359265596471)
    ·
      refine ⟨327311956617537538898394707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218207971078358359265596471 327311956617537538898394707)
      ·
        refine ⟨490967934926306308347592061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327311956617537538898394707 490967934926306308347592061)
        ·
          refine ⟨184112975597364865630347023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490967934926306308347592061 184112975597364865630347023)
          ·
            refine ⟨276169463396047298445520535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184112975597364865630347023 276169463396047298445520535)
            ·
              refine ⟨414254195094070947668280803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276169463396047298445520535 414254195094070947668280803)
              ·
                refine ⟨621381292641106421502421205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414254195094070947668280803 621381292641106421502421205)
                ·
                  refine ⟨14563624046275931753962997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 621381292641106421502421205 14563624046275931753962997)
                  ·
                    refine ⟨1365339754338368601934031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14563624046275931753962997 1365339754338368601934031)
                    ·
                      rfl

theorem cell23_7976969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 5].length) (baseStart_7976969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976969 prefixEnd_7976969 := by exact prefixLift 7976969
  have htrace : WordTrace (prefixWord ++ tailWord_7976969) baseStart_7976969 baseEnd_7976969 := by
    simpa [prefixWord, tailWord_7976969, baseEnd_7976969] using wordTrace_append hprefix tailTrace_7976969
  have hstable : (prefixWord ++ tailWord_7976969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976969).length < 2 ^ (prefixWord ++ tailWord_7976969).sum := by decide
  have hdescent : baseEnd_7976969 < baseStart_7976969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977010 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2]
def baseStart_7977010 : Nat := 118140960795 + 7977010 * 2 ^ 59
def prefixEnd_7977010 : Nat := 4983230072969 + 3 ^ 40 * 7977010 * 2
def baseEnd_7977010 : Nat := 4096040315721940145389405

theorem tailTrace_7977010 : CollatzResearch.WordTrace tailWord_7977010 prefixEnd_7977010 4096040315721940145389405 := by
  unfold tailWord_7977010
  simp only [CollatzResearch.WordTrace]
  refine ⟨72736364207665652422426121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193963637887108406459802989 72736364207665652422426121)
  ·
    refine ⟨54552273155749239316819591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72736364207665652422426121 54552273155749239316819591)
    ·
      refine ⟨81828409733623858975229387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54552273155749239316819591 81828409733623858975229387)
      ·
        refine ⟨122742614600435788462844081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81828409733623858975229387 122742614600435788462844081)
        ·
          refine ⟨92056960950326841347133061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122742614600435788462844081 92056960950326841347133061)
          ·
            refine ⟨17260680178186282752587449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92056960950326841347133061 17260680178186282752587449)
            ·
              refine ⟨12945510133639712064440587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17260680178186282752587449 12945510133639712064440587)
              ·
                refine ⟨19418265200459568096660881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12945510133639712064440587 19418265200459568096660881)
                ·
                  refine ⟨14563698900344676072495661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19418265200459568096660881 14563698900344676072495661)
                  ·
                    refine ⟨5461387087629253527185873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14563698900344676072495661 5461387087629253527185873)
                    ·
                      refine ⟨4096040315721940145389405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461387087629253527185873 4096040315721940145389405)
                      ·
                        rfl

theorem cell23_7977010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_7977010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977010 prefixEnd_7977010 := by exact prefixLift 7977010
  have htrace : WordTrace (prefixWord ++ tailWord_7977010) baseStart_7977010 baseEnd_7977010 := by
    simpa [prefixWord, tailWord_7977010, baseEnd_7977010] using wordTrace_append hprefix tailTrace_7977010
  have hstable : (prefixWord ++ tailWord_7977010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977010).length < 2 ^ (prefixWord ++ tailWord_7977010).sum := by decide
  have hdescent : baseEnd_7977010 < baseStart_7977010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977033 : List Nat := [1, 2, 1, 1, 2, 2, 6, 2, 2, 4]
def baseStart_7977033 : Nat := 118140960795 + 7977033 * 2 ^ 59
def prefixEnd_7977033 : Nat := 4983230072969 + 3 ^ 40 * 7977033 * 2
def baseEnd_7977033 : Nat := 1365350708592331185133933

theorem tailTrace_7977033 : CollatzResearch.WordTrace tailWord_7977033 prefixEnd_7977033 1365350708592331185133933 := by
  unfold tailWord_7977033
  simp only [CollatzResearch.WordTrace]
  refine ⟨290946295709579284617791753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193964197139719523078527835 290946295709579284617791753)
  ·
    refine ⟨218209721782184463463343815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290946295709579284617791753 218209721782184463463343815)
    ·
      refine ⟨327314582673276695195015723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218209721782184463463343815 327314582673276695195015723)
      ·
        refine ⟨490971874009915042792523585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327314582673276695195015723 490971874009915042792523585)
        ·
          refine ⟨368228905507436282094392689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490971874009915042792523585 368228905507436282094392689)
          ·
            refine ⟨276171679130577211570794517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368228905507436282094392689 276171679130577211570794517)
            ·
              refine ⟨12945547459245806792380993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 276171679130577211570794517 12945547459245806792380993)
              ·
                refine ⟨9709160594434355094285745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12945547459245806792380993 9709160594434355094285745)
                ·
                  refine ⟨7281870445825766320714309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9709160594434355094285745 7281870445825766320714309)
                  ·
                    refine ⟨1365350708592331185133933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7281870445825766320714309 1365350708592331185133933)
                    ·
                      rfl

theorem cell23_7977033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 4].length) (baseStart_7977033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977033 prefixEnd_7977033 := by exact prefixLift 7977033
  have htrace : WordTrace (prefixWord ++ tailWord_7977033) baseStart_7977033 baseEnd_7977033 := by
    simpa [prefixWord, tailWord_7977033, baseEnd_7977033] using wordTrace_append hprefix tailTrace_7977033
  have hstable : (prefixWord ++ tailWord_7977033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977033).length < 2 ^ (prefixWord ++ tailWord_7977033).sum := by decide
  have hdescent : baseEnd_7977033 < baseStart_7977033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977073 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 4, 1, 3]
def baseStart_7977073 : Nat := 118140960795 + 7977073 * 2 ^ 59
def prefixEnd_7977073 : Nat := 4983230072969 + 3 ^ 40 * 7977073 * 2
def baseEnd_7977073 : Nat := 4096072665003173398901615

theorem tailTrace_7977073 : CollatzResearch.WordTrace tailWord_7977073 prefixEnd_7977073 4096072665003173398901615 := by
  unfold tailWord_7977073
  simp only [CollatzResearch.WordTrace]
  refine ⟨290947754629434371449247873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193965169752956247632831915 290947754629434371449247873)
  ·
    refine ⟨218210815972075778586935905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290947754629434371449247873 218210815972075778586935905)
    ·
      refine ⟨163658111979056833940201929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218210815972075778586935905 163658111979056833940201929)
      ·
        refine ⟨122743583984292625455151447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163658111979056833940201929 122743583984292625455151447)
        ·
          refine ⟨184115375976438938182727171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122743583984292625455151447 184115375976438938182727171)
          ·
            refine ⟨276173063964658407274090757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184115375976438938182727171 276173063964658407274090757)
            ·
              refine ⟨51782449493373451363892017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276173063964658407274090757 51782449493373451363892017)
              ·
                refine ⟨38836837120030088522919013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51782449493373451363892017 38836837120030088522919013)
                ·
                  refine ⟨7281906960005641598047315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38836837120030088522919013 7281906960005641598047315)
                  ·
                    refine ⟨10922860440008462397070973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7281906960005641598047315 10922860440008462397070973)
                    ·
                      refine ⟨4096072665003173398901615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10922860440008462397070973 4096072665003173398901615)
                      ·
                        rfl

theorem cell23_7977073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_7977073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977073 prefixEnd_7977073 := by exact prefixLift 7977073
  have htrace : WordTrace (prefixWord ++ tailWord_7977073) baseStart_7977073 baseEnd_7977073 := by
    simpa [prefixWord, tailWord_7977073, baseEnd_7977073] using wordTrace_append hprefix tailTrace_7977073
  have hstable : (prefixWord ++ tailWord_7977073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977073).length < 2 ^ (prefixWord ++ tailWord_7977073).sum := by decide
  have hdescent : baseEnd_7977073 < baseStart_7977073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977074 : List Nat := [3, 2, 1, 2, 2, 3, 2, 3, 1, 2, 2]
def baseStart_7977074 : Nat := 118140960795 + 7977074 * 2 ^ 59
def prefixEnd_7977074 : Nat := 4983230072969 + 3 ^ 40 * 7977074 * 2
def baseEnd_7977074 : Nat := 4096073178483827894989111

theorem tailTrace_7977074 : CollatzResearch.WordTrace tailWord_7977074 prefixEnd_7977074 4096073178483827894989111 := by
  unfold tailWord_7977074
  simp only [CollatzResearch.WordTrace]
  refine ⟨72736947775607687155008569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193965194068287165746689517 72736947775607687155008569)
  ·
    refine ⟨54552710831705765366256427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72736947775607687155008569 54552710831705765366256427)
    ·
      refine ⟨81829066247558648049384641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54552710831705765366256427 81829066247558648049384641)
      ·
        refine ⟨61371799685668986037038481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81829066247558648049384641 61371799685668986037038481)
        ·
          refine ⟨46028849764251739527778861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61371799685668986037038481 46028849764251739527778861)
          ·
            refine ⟨17260818661594402322917073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46028849764251739527778861 17260818661594402322917073)
            ·
              refine ⟨12945613996195801742187805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17260818661594402322917073 12945613996195801742187805)
              ·
                refine ⟨4854605248573425653320427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12945613996195801742187805 4854605248573425653320427)
                ·
                  refine ⟨7281907872860138479980641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854605248573425653320427 7281907872860138479980641)
                  ·
                    refine ⟨5461430904645103859985481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7281907872860138479980641 5461430904645103859985481)
                    ·
                      refine ⟨4096073178483827894989111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461430904645103859985481 4096073178483827894989111)
                      ·
                        rfl

theorem cell23_7977074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_7977074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977074 prefixEnd_7977074 := by exact prefixLift 7977074
  have htrace : WordTrace (prefixWord ++ tailWord_7977074) baseStart_7977074 baseEnd_7977074 := by
    simpa [prefixWord, tailWord_7977074, baseEnd_7977074] using wordTrace_append hprefix tailTrace_7977074
  have hstable : (prefixWord ++ tailWord_7977074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977074).length < 2 ^ (prefixWord ++ tailWord_7977074).sum := by decide
  have hdescent : baseEnd_7977074 < baseStart_7977074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977117 : List Nat := [1, 4, 2, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_7977117 : Nat := 118140960795 + 7977117 * 2 ^ 59
def prefixEnd_7977117 : Nat := 4983230072969 + 3 ^ 40 * 7977117 * 2
def baseEnd_7977117 : Nat := 4096095258151971226751413

theorem tailTrace_7977117 : CollatzResearch.WordTrace tailWord_7977117 prefixEnd_7977117 4096095258151971226751413 := by
  unfold tailWord_7977117
  simp only [CollatzResearch.WordTrace]
  refine ⟨290949359441274966963849605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193966239627516644642566403 290949359441274966963849605)
  ·
    refine ⟨54553004895239056305721801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290949359441274966963849605 54553004895239056305721801)
    ·
      refine ⟨40914753671429292229291351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54553004895239056305721801 40914753671429292229291351)
      ·
        refine ⟨61372130507143938343937027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40914753671429292229291351 61372130507143938343937027)
        ·
          refine ⟨92058195760715907515905541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61372130507143938343937027 92058195760715907515905541)
          ·
            refine ⟨17260911705134232659232289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92058195760715907515905541 17260911705134232659232289)
            ·
              refine ⟨12945683778850674494424217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17260911705134232659232289 12945683778850674494424217)
              ·
                refine ⟨9709262834138005870818163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12945683778850674494424217 9709262834138005870818163)
                ·
                  refine ⟨14563894251207008806227245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9709262834138005870818163 14563894251207008806227245)
                  ·
                    refine ⟨5461460344202628302335217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14563894251207008806227245 5461460344202628302335217)
                    ·
                      refine ⟨4096095258151971226751413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461460344202628302335217 4096095258151971226751413)
                      ·
                        rfl

theorem cell23_7977117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_7977117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977117 prefixEnd_7977117 := by exact prefixLift 7977117
  have htrace : WordTrace (prefixWord ++ tailWord_7977117) baseStart_7977117 baseEnd_7977117 := by
    simpa [prefixWord, tailWord_7977117, baseEnd_7977117] using wordTrace_append hprefix tailTrace_7977117
  have hstable : (prefixWord ++ tailWord_7977117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977117).length < 2 ^ (prefixWord ++ tailWord_7977117).sum := by decide
  have hdescent : baseEnd_7977117 < baseStart_7977117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977133 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_7977133 : Nat := 118140960795 + 7977133 * 2 ^ 59
def prefixEnd_7977133 : Nat := 4983230072969 + 3 ^ 40 * 7977133 * 2
def baseEnd_7977133 : Nat := 4096103473842443164151339

theorem tailTrace_7977133 : CollatzResearch.WordTrace tailWord_7977133 prefixEnd_7977133 4096103473842443164151339 := by
  unfold tailWord_7977133
  simp only [CollatzResearch.WordTrace]
  refine ⟨290949943009217001696432053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193966628672811334464288035 290949943009217001696432053)
  ·
    refine ⟨27276557157114093909040505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 290949943009217001696432053 27276557157114093909040505)
    ·
      refine ⟨20457417867835570431780379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27276557157114093909040505 20457417867835570431780379)
      ·
        refine ⟨30686126801753355647670569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20457417867835570431780379 30686126801753355647670569)
        ·
          refine ⟨23014595101315016735752927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30686126801753355647670569 23014595101315016735752927)
          ·
            refine ⟨34521892651972525103629391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23014595101315016735752927 34521892651972525103629391)
            ·
              refine ⟨51782838977958787655444087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34521892651972525103629391 51782838977958787655444087)
              ·
                refine ⟨77674258466938181483166131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51782838977958787655444087 77674258466938181483166131)
                ·
                  refine ⟨116511387700407272224749197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77674258466938181483166131 116511387700407272224749197)
                  ·
                    refine ⟨43691770387652727084280949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116511387700407272224749197 43691770387652727084280949)
                    ·
                      refine ⟨4096103473842443164151339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43691770387652727084280949 4096103473842443164151339)
                      ·
                        rfl

theorem cell23_7977133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_7977133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977133 prefixEnd_7977133 := by exact prefixLift 7977133
  have htrace : WordTrace (prefixWord ++ tailWord_7977133) baseStart_7977133 baseEnd_7977133 := by
    simpa [prefixWord, tailWord_7977133, baseEnd_7977133] using wordTrace_append hprefix tailTrace_7977133
  have hstable : (prefixWord ++ tailWord_7977133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977133).length < 2 ^ (prefixWord ++ tailWord_7977133).sum := by decide
  have hdescent : baseEnd_7977133 < baseStart_7977133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
